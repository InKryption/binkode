const std = @import("std");

pub const varint = @import("varint.zig");

const std_codec = @import("std_codec.zig");
pub const StdCodec = std_codec.StdCodec;

pub const std_reflect = @import("std_reflect.zig");

comptime {
    _ = varint;
    _ = std_codec;
    _ = std_reflect;
}

pub const IntEncoding = enum {
    fixint,
    varint,
};

pub const Config = struct {
    endian: std.builtin.Endian,
    int: IntEncoding,

    pub const default: Config = .{
        .endian = .little,
        .int = .varint,
    };

    pub inline fn cfg(
        endian: std.builtin.Endian,
        int: IntEncoding,
    ) Config {
        return .{
            .endian = endian,
            .int = int,
        };
    }
};

pub const EncodedCounts = struct {
    /// The number of values which were fully encoded to the writer.
    value_count: usize,
    /// The number of encoded bytes; this may be nonzero even when `value_count` is zero,
    /// since it also includes bytes from partial writes of values.
    byte_count: usize,
};

pub const EncodeError = error{
    /// Codec implementation failed to encode value.
    EncodeFailed,
};

pub const DecodeError = error{
    /// Codec implementation failed to decode value.
    DecodeFailed,
};

pub const EncodeToWriterError = EncodeError || std.Io.Writer.Error;
pub const EncodeToSliceError = EncodeError || error{NoSpaceLeft};
pub const DecodeFromReaderError = DecodeError || std.mem.Allocator.Error || std.Io.Reader.Error;
pub const DecodeFromSliceError = DecodeError || std.mem.Allocator.Error || error{EndOfStream};
pub const DecodeSkipError = DecodeError || std.Io.Reader.Error;

/// This represents an encoding & decoding scheme for a value of type `V`.
/// It is effectively a comptime-known VTable, which allows making different `Codec(V)`s
/// interchangeable, and therefore easily composable, while still being static, avoiding
/// the overhead of runtime dispatch.
/// Includes type fields for specifying additional context at runtime if necessary.
pub fn Codec(comptime V: type) type {
    return struct {
        /// The type of the context consumed by `encodeFn`.
        EncodeCtx: type,

        /// Encodes all `values[i]` to the `writer` stream sequentially, in a manner defined by the implementation.
        /// The implementation should treat each `values[i]` as independent from all other `values[j]`.
        ///
        /// Returns the number of `values` that were successfully encoded, and the number of encoded bytes that were
        /// written; implementations may choose to encode however many values they want to.
        ///
        /// If `limit == .unlimited`, the implementation is obligated to write a minimum of one value.
        /// If `limit != .unlimited`, the implementation may write one or more values, or zero if one whole value
        /// would not fit within the specified limit; if zero values are written, the implementation must have written
        /// a non-zero number of encoded bytes.
        ///
        /// The implementation is allowed to assume/assert the following invariants:
        /// * `values.len != 0`.
        /// * `limit >= encode_min_size`.
        /// * `progress_stack` is `@splat(0)`, or it was updated by a previous call to `encodeFn`.
        /// * If `limit != .unlimited` and `encode_stack_size != 0`, `progress_stack != null`.
        encodeFn: fn (
            writer: *std.Io.Writer,
            config: Config,
            values: []const V,
            /// Must be a value of type `?*[encode_stack_size]u64`.
            /// If non-null, and `encode_stack_size != 0`, `progress_stack[n]` can be used by
            /// the implementation to store encoding progress at a given level of nesting.
            /// Once all highest indices of the stack have reset to zero, the parent nested
            /// index should also reset to zero.
            ///
            /// For example: if the implementation encodes array values, but the given `limit`
            /// does not permit encoding all elements of the array at `values[0]`, `progress_stack[0]`
            /// should be used to store the index of the last element that wasn't (fully) encoded,
            /// such that the subsequent call would observe that index, and resume encoding starting
            /// from that element.
            ///
            /// NOTE: this should not be used to keep track of the index in `values`, since
            /// this slice parameter will be truncated in subsequent calls as the return
            /// value's `value_count` field permits.
            ///
            /// `@splat(0)` is the initial valid state.
            progress_stack: anytype,
            /// The maximum number of bytes the implementation is allowed to write to `writer`.
            limit: std.Io.Limit,
            /// Must be a value of type `EncodeCtx`.
            ctx: anytype,
        ) EncodeToWriterError!EncodedCounts,

        /// The minimum number of encoded bytes that `encodeFn` must be allowed to write.
        /// The implementation may still write fewer encoded bytes than this.
        encode_min_size: usize,

        /// The size of the progress stack used by `encodeFn`.
        encode_stack_size: usize,

        /// The type of the context consumed by `decodeInitFn`, `decodeFn`, and `freeFn`.
        DecodeCtx: type,

        /// Initializes all `values[i]` in preparation for each being passed to `decodeFn`.
        /// Should act as a semantic memset, where each `values[i]` is initialized independent
        /// of each other; this should be a memset in the sense that each value is considered
        /// to be in the same "state", but not necessarily the same exact bit pattern. For example,
        /// where `V = *T`, each `values[i]` would generally be a distinct pointer from each
        /// other `values[i]`, but pointing to similar, albeit equally independent data.
        /// The rationale for this design is to permit the implementation to define optimal
        /// initialization for batches of values.
        /// The implementation must clean up any resources it allocated if it fails to complete,
        /// leaving all `values[i]` in an undefined state.
        ///
        /// The implementation should document the the resulting value, and any other
        /// states it would consider valid for the purposes of in-place decoding, which
        /// must also be legal to pass to `freeFn`.
        /// The initial state should, conventionally, be some simple "empty" permutation.
        ///
        /// If this is null, the implementation assumes it will be overwriting undefined data in `decodeFn`.
        ///
        /// The implementation is allowed to assume/assert the following invariants:
        /// * `values.len != 0`.
        decodeInitFn: ?fn (
            gpa_opt: ?std.mem.Allocator,
            /// Should be assumed to be undefined by the implementation, which should set
            /// it to a valid initial state for `decodeFn` to consume and decode into.
            values: []V,
            /// Must be a value of type `DecodeCtx`.
            ctx: anytype,
        ) std.mem.Allocator.Error!void,

        /// Decodes a sequential list of values to fill `values`, in a manner defined by the implementation.
        /// The implementation should treat each `values[i]` as independent from all other `values[j]`.
        ///
        /// The number of valid decoded items is written to `decoded_count.*`, such that
        /// the slice `values[0..decoded_count.*]` is all valid decoded values, which must be
        /// freed by the caller.
        /// `values[decoded_count.*..]` is only expected to be comprised of valid values if
        /// `decodeInitFn != null`; if it is, the caller is also responsible for freeing it.
        ///
        /// The implementation is allowed to assume/assert the following invariants:
        /// * `values.len != 0`.
        /// * `decoded_count.* == 0`, initially.
        decodeFn: fn (
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            /// If `decodeInitFn == null`, expected to point to undefined data, to be initialized.
            ///
            /// If `decodeInitFn != null`, expected to either have been initialized
            /// by `decodeInitFn`, or otherwise to be conformant with the documented
            /// expectations of the implementation.
            values: []V,
            /// Output parameter for the number of values successfully decoded.
            /// The only circumstance in which `values.len != decoded_count.*` is when an error returns.
            /// Assume `decoded_count.* <= values.len`.
            decoded_count: *usize,
            /// Must be a value of type `DecodeCtx`.
            ctx: anytype,
        ) DecodeFromReaderError!void,

        /// Similar to `decodeFn`, decodes a sequential list of `value_count` values, in a manner defined
        /// by the implementation. This should behave the same as calling `decodeFn`, and then immediately
        /// discarding the result, except without the need to store the data.
        ///
        /// The implementation is allowed to assume/assert the following invariants:
        /// * `values.len != 0`.
        /// * `decoded_count.* != 0`, initially.
        decodeSkipFn: fn (
            reader: *std.Io.Reader,
            config: Config,
            value_count: usize,
            /// Output parameter for the number of values successfully skipped.
            /// The only circumstance in which `values.len != decoded_count.*` is when an error returns.
            /// Assume `decoded_count.* <= values.len`.
            decoded_count: *usize,
            /// Must be a value of type `DecodeCtx`.
            ctx: anytype,
        ) DecodeSkipError!void,

        /// Frees any of the resources held by each `value[i]`.
        /// Assumes `value[i]` is in a valid state as defined by the implementation,
        /// meaning it must be able to free any value produced by a successful call
        /// to `decodeInitFn` and `decodeFn`.
        /// If this is null, the `free` method is a noop, meaning the implementation does not
        /// need to free any resources.
        ///
        /// The implementation is allowed to assume/assert the following invariants:
        /// * `values.len != 0`.
        freeFn: ?fn (
            gpa_opt: ?std.mem.Allocator,
            values: []const V,
            /// Must be a value of type `DecodeCtx`.
            ctx: anytype,
        ) void,
        const CodecSelf = @This();

        /// Encodes `value.*` to the `writer` stream.
        pub fn encode(
            self: CodecSelf,
            writer: *std.Io.Writer,
            config: Config,
            value: *const V,
            ctx: self.EncodeCtx,
        ) EncodeToWriterError!void {
            try self.encodeMany(writer, config, @ptrCast(value), ctx);
        }

        /// Encodes each `values[i]` to the `writer` stream sequentially.
        pub fn encodeMany(
            self: CodecSelf,
            writer: *std.Io.Writer,
            config: Config,
            values: []const V,
            ctx: self.EncodeCtx,
        ) EncodeToWriterError!void {
            if (values.len == 0) return;

            // since each partial call must encode a minimum of one value,
            // there is an upper bound on these iterations of `values.len`.
            var value_count: usize = 0;
            for (0..values.len) |_| {
                const remaining = values[value_count..];
                const counts = try self.encodeManyPartialRaw(writer, config, remaining, null, .unlimited, ctx);
                // sanity checks
                std.debug.assert(counts.value_count != 0);
                std.debug.assert(counts.value_count <= remaining.len);
                std.debug.assert(value_count + counts.value_count <= values.len);
                value_count += counts.value_count;
                if (value_count == values.len) break;
            } else unreachable;
        }

        pub fn encodeOnePartialRaw(
            self: CodecSelf,
            writer: *std.Io.Writer,
            config: Config,
            value: *const V,
            progress_stack: ?*[self.encode_stack_size]u64,
            limit: std.Io.Limit,
            ctx: self.EncodeCtx,
        ) EncodeToWriterError!EncodedCounts {
            return self.encodeManyPartialRaw(
                writer,
                config,
                @ptrCast(value),
                progress_stack,
                limit,
                ctx,
            );
        }

        pub fn encodeManyPartialRaw(
            self: CodecSelf,
            writer: *std.Io.Writer,
            config: Config,
            values: []const V,
            progress_stack: ?*[self.encode_stack_size]u64,
            limit: std.Io.Limit,
            ctx: self.EncodeCtx,
        ) EncodeToWriterError!EncodedCounts {
            if (limit.toInt()) |byte_limit| {
                std.debug.assert(byte_limit >= self.encode_min_size);
            }

            switch (limit) {
                .unlimited => std.debug.assert(progress_stack == null),
                .nothing, _ => std.debug.assert(self.encode_stack_size == 0 or progress_stack != null),
            }

            if (values.len == 0) return .{
                .value_count = 0,
                .byte_count = 0,
            };

            const counts = try self.encodeFn(writer, config, values, progress_stack, limit, ctx);
            std.debug.assert(counts.value_count <= values.len);
            if (limit.toInt()) |byte_limit| {
                std.debug.assert(counts.byte_count <= byte_limit);
                std.debug.assert(counts.byte_count != 0 or counts.value_count != 0);
            } else {
                std.debug.assert(counts.value_count != 0);
            }
            return counts;
        }

        /// Returns the number of bytes occupied by the encoded representation of `value.*`.
        pub fn encodedSize(
            self: CodecSelf,
            config: Config,
            value: *const V,
            ctx: self.EncodeCtx,
        ) EncodeError!u64 {
            var discarding: std.Io.Writer.Discarding = .init(&.{});
            const writer = &discarding.writer;
            self.encode(writer, config, value, ctx) catch |err| switch (err) {
                error.EncodeFailed => |e| return e,
                error.WriteFailed => unreachable, // discarding writer shouldn't fail here
            };
            return discarding.fullCount();
        }

        /// Encodes `value.*` to `slice`, returning the length of the encoded data in it.
        /// Returns `error.WriteFailed` if `slice` is not large enough to hold the full
        /// encoded representation of `value.*`, ie if `slice.len < self.encodedSize(config, value)`.
        pub fn encodeToSlice(
            self: CodecSelf,
            slice: []u8,
            config: Config,
            value: *const V,
            ctx: self.EncodeCtx,
        ) EncodeToSliceError!usize {
            var fixed_writer: std.Io.Writer = .fixed(slice);
            self.encode(&fixed_writer, config, value, ctx) catch |err| switch (err) {
                error.EncodeFailed => |e| return e,
                error.WriteFailed => return error.NoSpaceLeft,
            };
            return fixed_writer.end;
        }

        /// Encodes `value.*`, returning the encoded representation in the returned slice allocated with with `gpa`.
        /// Conveniently translates `error.WriteFailed` into `error.OutOfMemory`.
        pub fn encodeAlloc(
            self: CodecSelf,
            gpa: std.mem.Allocator,
            config: Config,
            value: *const V,
            ctx: self.EncodeCtx,
        ) (EncodeError || std.mem.Allocator.Error)![]u8 {
            var list: std.ArrayList(u8) = .empty;
            defer list.deinit(gpa);
            try self.encodeToArrayList(gpa, &list, config, value, ctx);
            return try list.toOwnedSlice(gpa);
        }

        /// Encodes `value.*`, appending the encoded representation to `list`, growing it with `gpa`.
        /// Conveniently translates `error.WriteFailed` into `error.OutOfMemory`.
        pub fn encodeToArrayList(
            self: CodecSelf,
            gpa: std.mem.Allocator,
            list: *std.ArrayList(u8),
            config: Config,
            value: *const V,
            ctx: self.EncodeCtx,
        ) (EncodeError || std.mem.Allocator.Error)!void {
            var allocating: std.Io.Writer.Allocating = .fromArrayList(gpa, list);
            defer list.* = allocating.toArrayList();
            const writer = &allocating.writer;
            self.encode(writer, config, value, ctx) catch |err| switch (err) {
                error.EncodeFailed => |e| return e,
                error.WriteFailed => return error.OutOfMemory, // the allocating writer's only failure is OOM
            };
        }

        /// Decodes the value from the `reader` stream and returns it.
        pub fn decode(
            self: CodecSelf,
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            ctx: self.DecodeCtx,
        ) DecodeFromReaderError!V {
            var value: V = undefined;
            try self.decodeInitOne(gpa_opt, &value, ctx);
            try self.decodeIntoOne(reader, gpa_opt, config, &value, ctx);
            return value;
        }

        /// Same as `decode`, but takes a slice directly as input.
        /// Returns the value, and the number of bytes which were
        /// consumed to decode the value.
        pub fn decodeSlice(
            self: CodecSelf,
            src: []const u8,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            ctx: self.DecodeCtx,
        ) DecodeFromSliceError!struct { V, usize } {
            var value: V = undefined;
            try self.decodeInitOne(gpa_opt, &value, ctx);
            const len = try self.decodeSliceInto(src, gpa_opt, config, &value, ctx);
            std.debug.assert(len <= src.len);
            return .{ value, len };
        }

        /// Same as `decode`, but takes a slice directly as input.
        /// Returns `error.Overlong` if the number of bytes which were
        /// consumed to decode the value do not match `src.len`.
        pub fn decodeSliceExact(
            self: CodecSelf,
            src: []const u8,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            ctx: self.DecodeCtx,
        ) (DecodeFromSliceError || error{Overlong})!V {
            const value, const len = try self.decodeSlice(src, gpa_opt, config, ctx);
            errdefer self.free(gpa_opt, &value, ctx);
            if (len != src.len) return error.Overlong;
            return value;
        }

        /// Same as `decodeSliceExact`, but ignores `error.Overlong`.
        pub fn decodeSliceIgnoreLength(
            self: CodecSelf,
            src: []const u8,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            ctx: self.DecodeCtx,
        ) DecodeFromSliceError!V {
            const value, _ = try self.decodeSlice(src, gpa_opt, config, ctx);
            return value;
        }

        /// Same as `decodeInitMany`, but for a single value.
        pub fn decodeInitOne(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            value: *V,
            ctx: self.DecodeCtx,
        ) std.mem.Allocator.Error!void {
            try self.decodeInitMany(gpa_opt, @ptrCast(value), ctx);
        }

        /// See the `decodeInitFn` field for important commentary on the implications
        /// of this and related functions.
        /// This is mainly relevant to codec implementations consuming other codecs.
        pub fn decodeInitMany(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            values: []V,
            ctx: self.DecodeCtx,
        ) std.mem.Allocator.Error!void {
            const decodeInitFn = self.decodeInitFn orelse return;
            if (values.len == 0) return;
            try decodeInitFn(gpa_opt, values, ctx);
        }

        /// Same as `decodeIntoOne`, but takes a slice directly as input.
        /// Returns the number of bytes in `src` which were consumed to decode into `value.*`.
        pub fn decodeSliceInto(
            self: CodecSelf,
            src: []const u8,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            value: *V,
            ctx: self.DecodeCtx,
        ) DecodeFromSliceError!usize {
            var reader: std.Io.Reader = .fixed(src);
            self.decodeIntoOne(&reader, gpa_opt, config, value, ctx) catch |err| switch (err) {
                error.DecodeFailed => |e| return e,
                error.OutOfMemory => |e| return e,
                error.EndOfStream => |e| return e,
                error.ReadFailed => unreachable, // fixed-buffer reader cannot fail, it only returns error.EndOfStream.
            };
            return reader.seek;
        }

        /// Same as `decodeIntoMany`, but for a single value.
        pub fn decodeIntoOne(
            self: CodecSelf,
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            value: *V,
            ctx: self.DecodeCtx,
        ) DecodeFromReaderError!void {
            try self.decodeIntoMany(reader, gpa_opt, config, @ptrCast(value), ctx);
        }

        /// Decodes into `values[i]` from the `reader` stream.
        ///
        /// If `decodeInitFn != null`, all `values[i]` must be in a defined state, because
        /// on error return, all `values[i]` will be freed and in an undefined state.
        /// If `decodeInitFn == null`, expects `values` to be in an undefined state, to
        /// be overwritten during decoding, and will remain in such a state on error return.
        ///
        /// See doc comments on `decodeFn` and `decodeInitFn` for commentary
        /// on the expected initial state of `values[i]`.
        pub fn decodeIntoMany(
            self: CodecSelf,
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            values: []V,
            ctx: self.DecodeCtx,
        ) DecodeFromReaderError!void {
            if (values.len == 0) return;
            var decoded_count: usize = 0;
            self.decodeIntoManyRaw(reader, gpa_opt, config, values, &decoded_count, ctx) catch |err| {
                const amt_to_free = if (self.decodeInitFn != null) values.len else decoded_count;
                self.freeMany(gpa_opt, values[0..amt_to_free], ctx);
                return err;
            };
        }

        /// This function mainly concerns Codec implementations consuming other Codecs.
        ///
        /// Decodes into `values[i]` from the `reader` stream, outputting the number
        /// of valid decoded elements that were written to it into `decoded_count.*`.
        ///
        /// See doc comments on `decodeFn` and `decodeInitFn` for commentary
        /// on the expected initial state of `values[i]`, and other more detailed info.
        pub fn decodeIntoManyRaw(
            self: CodecSelf,
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            values: []V,
            decoded_count: *usize,
            ctx: self.DecodeCtx,
        ) DecodeFromReaderError!void {
            decoded_count.* = 0;
            if (values.len == 0) return;
            defer std.debug.assert(decoded_count.* <= values.len);
            try self.decodeFn(reader, gpa_opt, config, values, decoded_count, ctx);
            if (decoded_count.* != values.len) std.debug.panic("{} != {}", .{ decoded_count.*, values.len });
            std.debug.assert(decoded_count.* == values.len);
        }

        /// Skips `value_count` values.
        pub fn decodeSkip(
            self: CodecSelf,
            reader: *std.Io.Reader,
            config: Config,
            value_count: usize,
            ctx: self.DecodeCtx,
        ) DecodeSkipError!void {
            var decoded_count: usize = 0;
            try self.decodeSkipManyRaw(reader, config, value_count, &decoded_count, ctx);
        }

        /// This function mainly concerns Codec implementations consuming other Codecs.
        ///
        /// Performs the same internal logic as `decodeIntoManyRaw`, except it does not store
        /// the decoded data to memory, and instead immediately discards everything, ideally
        /// in an efficient manner.
        pub fn decodeSkipManyRaw(
            self: CodecSelf,
            reader: *std.Io.Reader,
            config: Config,
            value_count: usize,
            decoded_count: *usize,
            ctx: self.DecodeCtx,
        ) DecodeSkipError!void {
            decoded_count.* = 0;
            if (value_count == 0) return;
            defer std.debug.assert(decoded_count.* <= value_count);
            try self.decodeSkipFn(reader, config, value_count, decoded_count, ctx);
            std.debug.assert(decoded_count.* == value_count);
        }

        /// Frees any of the resources held by `value.*`.
        /// Expects `value.*` to be in a valid state as defined by the implementation.
        /// Does not free the `value` as a pointer.
        pub fn free(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            value: *const V,
            ctx: self.DecodeCtx,
        ) void {
            self.freeMany(gpa_opt, @ptrCast(value), ctx);
        }

        pub fn freeMany(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            values: []const V,
            ctx: self.DecodeCtx,
        ) void {
            const freeFn = self.freeFn orelse return;
            if (values.len == 0) return;
            freeFn(gpa_opt, values, ctx);
        }

        pub const Standard = StdCodec(V);

        /// Construct a codec from a composition of standard codecs for an assortment of types,
        /// defined to behave in line with the bincode specification.
        pub fn standard(constructor: Standard) CodecSelf {
            return constructor.codec;
        }

        pub fn EncodedReader(codec: CodecSelf) type {
            return struct {
                interface: std.Io.Reader,
                value_fbw: std.Io.Writer,
                config: Config,
                ctx: codec.EncodeCtx,
                values: []const V,
                value_count: usize,
                progress_stack: *[codec.encode_stack_size]u64,
                const EncodedReaderSelf = @This();

                pub const InitParams = struct {
                    reader_buffer: []u8,
                    /// Asserted to be `.len >= codec.encode_min_size`.
                    value_buffer: []u8,
                    progress_stack: *[codec.encode_stack_size]u64,
                    config: Config,
                    ctx: codec.EncodeCtx,
                };

                pub fn initOne(
                    value: *const V,
                    params: InitParams,
                ) EncodedReaderSelf {
                    return .initMany(@ptrCast(value), params);
                }

                pub fn initMany(
                    values: []const V,
                    params: InitParams,
                ) EncodedReaderSelf {
                    std.debug.assert(params.value_buffer.len >= codec.encode_min_size);
                    return .{
                        .interface = .{
                            .vtable = &vtable,
                            .buffer = params.reader_buffer,
                            .seek = 0,
                            .end = 0,
                        },
                        .value_fbw = .fixed(params.value_buffer),
                        .config = params.config,
                        .ctx = params.ctx,
                        .values = values,
                        .value_count = 0,
                        .progress_stack = params.progress_stack,
                    };
                }

                pub fn reset(self: *EncodedReaderSelf) void {
                    self.interface.seek = 0;
                    self.interface.end = 0;
                    self.value_fbw.end = 0;
                    self.value_count = 0;
                    @memset(self.progress_stack, 0);
                }

                const vtable: std.Io.Reader.VTable = .{
                    .stream = stream,
                };

                fn stream(
                    r: *std.Io.Reader,
                    w: *std.Io.Writer,
                    limit: std.Io.Limit,
                ) std.Io.Reader.StreamError!usize {
                    const self: *EncodedReaderSelf = @fieldParentPtr("interface", r);

                    if (self.value_count == self.values.len and self.value_fbw.end == 0) {
                        return error.EndOfStream;
                    }

                    const buffered_consumed_count = limit.minInt(self.value_fbw.end);
                    const remaining_limit = limit.subtract(buffered_consumed_count).?;
                    try w.writeAll(limit.sliceConst(self.value_fbw.buffered()));
                    _ = self.value_fbw.consume(buffered_consumed_count);

                    if (remaining_limit.toInt()) |byte_limit| {
                        if (byte_limit < codec.encode_min_size) {
                            if (self.value_fbw.unusedCapacityLen() >= codec.encode_min_size) {
                                const counts = codec.encodeManyPartialRaw(
                                    &self.value_fbw,
                                    self.config,
                                    self.values[self.value_count..],
                                    self.progress_stack,
                                    .limited(self.value_fbw.unusedCapacityLen()),
                                    self.ctx,
                                ) catch |err| switch (err) {
                                    error.EncodeFailed => return error.ReadFailed,
                                    error.WriteFailed => |e| return e,
                                };
                                self.value_count += counts.value_count;
                            }
                            return buffered_consumed_count;
                        }
                    }

                    const counts = codec.encodeManyPartialRaw(
                        w,
                        self.config,
                        self.values[self.value_count..],
                        self.progress_stack,
                        remaining_limit,
                        self.ctx,
                    ) catch |err| switch (err) {
                        error.EncodeFailed => return error.ReadFailed,
                        error.WriteFailed => |e| return e,
                    };
                    self.value_count += counts.value_count;
                    return buffered_consumed_count + counts.byte_count;
                }
            };
        }

        // -- Helpers for safely implementing common codecs -- //

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, config: Config, gpa_opt: ?std.mem.Allocator, values: []const V, ctx: EncodeCtx) EncodeWriterError!void { ... }
        /// fn decodeInit(gpa_opt: ?std.mem.Allocator, values: []V, ctx: DecodeCtx) std.mem.Allocator.Error!void { ... }
        /// fn decode(reader: *std.Io.Reader, config: Config, gpa_opt: ?std.mem.Allocator, value: *V, ctx: DecodeCtx) DecodeReaderError!void { ... }
        /// fn free(gpa_opt: ?std.mem.Allocator, value: *const V, ctx: DecodeCtx) void { ... }
        /// ```
        pub fn implement(
            comptime EncodeCtx: type,
            comptime DecodeCtx: type,
            comptime methods: type,
        ) CodecSelf {
            const erased = ImplementMethods(EncodeCtx, DecodeCtx, methods);
            return .{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,
                .encode_min_size = erased.encode_min_size,
                .encode_stack_size = erased.encode_stack_size,

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = if (@TypeOf(methods.decodeInit) != @TypeOf(null)) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .decodeSkipFn = erased.decodeSkip,
                .freeFn = if (@TypeOf(methods.free) != @TypeOf(null)) erased.free else null,
            };
        }

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, config: Config, gpa_opt: ?std.mem.Allocator, values: []const V, ctx: EncodeCtx) EncodeWriterError!void { ... }
        /// fn decodeInit(gpa_opt: ?std.mem.Allocator, values: []V, ctx: DecodeCtx) std.mem.Allocator.Error!void { ... }
        /// fn decode(reader: *std.Io.Reader, config: Config, gpa_opt: ?std.mem.Allocator, value: *V, ctx: DecodeCtx) DecodeReaderError!void { ... }
        /// fn free(gpa_opt: ?std.mem.Allocator, value: *const V, ctx: DecodeCtx) void { ... }
        /// ```
        pub fn ImplementMethods(
            comptime EncodeCtx: type,
            comptime DecodeCtx: type,
            comptime methods: type,
        ) type {
            return struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: anytype,
                ) EncodeToWriterError!EncodedCounts {
                    if (@TypeOf(ctx) != EncodeCtx) @compileError(
                        "Expected type " ++ @typeName(EncodeCtx) ++ ", got " ++ @typeName(@TypeOf(ctx)),
                    );
                    std.debug.assert(values.len != 0);
                    if (limit.toInt()) |byte_limit| {
                        std.debug.assert(byte_limit >= encode_min_size);
                    }
                    return try methods.encode(writer, config, values, progress_stack, limit, ctx);
                }

                pub const encode_min_size: usize = methods.encode_min_size;

                pub const encode_stack_size: usize = methods.encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: anytype,
                ) std.mem.Allocator.Error!void {
                    if (@TypeOf(ctx) != DecodeCtx) @compileError(
                        "Expected type " ++ @typeName(DecodeCtx) ++ ", got " ++ @typeName(@TypeOf(ctx)),
                    );
                    std.debug.assert(values.len != 0);
                    try methods.decodeInit(gpa_opt, values, ctx);
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    gpa_opt: ?std.mem.Allocator,
                    config: Config,
                    values: []V,
                    decoded_count: *usize,
                    ctx: anytype,
                ) DecodeFromReaderError!void {
                    if (@TypeOf(ctx) != DecodeCtx) @compileError(
                        "Expected type " ++ @typeName(DecodeCtx) ++ ", got " ++ @typeName(@TypeOf(ctx)),
                    );
                    std.debug.assert(values.len != 0);
                    std.debug.assert(decoded_count.* == 0);
                    try methods.decode(reader, config, gpa_opt, values, decoded_count, ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: Config,
                    value_count: usize,
                    /// Output parameter for the number of values successfully skipped.
                    /// The only circumstance in which `values.len != decoded_count.*` is when an error returns.
                    /// Assume `decoded_count.* <= values.len`.
                    decoded_count: *usize,
                    /// Must be a value of type `DecodeCtx`.
                    ctx: anytype,
                ) DecodeSkipError!void {
                    if (@TypeOf(ctx) != DecodeCtx) @compileError(
                        "Expected type " ++ @typeName(DecodeCtx) ++ ", got " ++ @typeName(@TypeOf(ctx)),
                    );
                    std.debug.assert(value_count != 0);
                    std.debug.assert(decoded_count.* == 0);
                    try methods.decodeSkip(reader, config, value_count, decoded_count, ctx);
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    values: []const V,
                    ctx: anytype,
                ) void {
                    if (@TypeOf(ctx) != DecodeCtx) @compileError(
                        "Expected type " ++ @typeName(DecodeCtx) ++ ", got " ++ @typeName(@TypeOf(ctx)),
                    );
                    std.debug.assert(values.len != 0);
                    methods.free(gpa_opt, values, ctx);
                }
            };
        }
    };
}

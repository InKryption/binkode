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
    varint,
    fixint,
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

pub const EncodeError = error{
    /// Codec implementation failed to encode value.
    EncodeFailed,
};

pub const DecodeError = error{
    /// Codec implementation failed to decode value.
    DecodeFailed,
};

pub const EncodeWriterError = EncodeError || std.Io.Writer.Error;
pub const DecodeReaderError = DecodeError || std.mem.Allocator.Error || std.Io.Reader.Error;
pub const DecodeSliceError = DecodeError || std.mem.Allocator.Error || error{EndOfStream};

/// This represents an encoding & decoding scheme for a value of type `V`.
/// It is effectively a comptime-known VTable, which allows making different `Codec(V)`s
/// interchangeable, and therefore easily composable, while still being static, avoiding
/// the overhead of runtime dispatch.
/// Includes type fields for specifying additional context at runtime if necessary.
pub fn Codec(comptime V: type) type {
    return struct {
        /// The type of the context consumed by `encodeFn`.
        EncodeCtx: type,

        /// Encodes `value.*` to the `writer` stream in a manner defined by the implementation.
        encodeFn: fn (
            writer: *std.Io.Writer,
            config: Config,
            value: *const V,
            /// Must point to a value of type `EncodeCtx`.
            ctx_ptr: *const anyopaque,
        ) EncodeWriterError!void,

        /// The type of the context consumed by `decodeInitFn`, `decodeFn`, and `freeFn`.
        DecodeCtx: type,

        /// Initializes all `values[i]` in preparation for each being passed to `decodeFn`.
        /// Should act as a semantic memset, where each `values[i]` is initialized independent
        /// of each other; this should be a memset in the sense that each value is considered
        /// to be in the same "state", but not necessarily the same exact bit pattern. For example,
        /// where `V = *T`, each `values[i]` should generally be a distinct pointer from each
        /// other `values[i]`, but pointing to similar, albeit equally independent data.
        /// The rationale for this design is to permit the implementation to define optimal
        /// initialization for batches of values.
        /// The implementation must clean up any resources it allocated if it fails to complete.
        ///
        /// The implementation should document the the resulting value, and any other
        /// states it would consider valid for the purposes of in-place decoding, which
        /// must also be legal to pass to `freeFn`.
        /// The initial state should, conventionally, be some simple "empty" permutation.
        ///
        /// If this is null, the implementation assumes it will be overwriting undefined data in `decodeFn`.
        decodeInitFn: ?fn (
            gpa_opt: ?std.mem.Allocator,
            /// Should be assumed to be undefined by the implementation, which should set
            /// it to a valid initial state for `decodeFn` to consume and decode into.
            values: []V,
            /// Must point to a value of type `DecodeCtx`.
            ctx_ptr: *const anyopaque,
        ) std.mem.Allocator.Error!void,

        /// Decodes into `value.*` from the `reader` stream.
        decodeFn: fn (
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            /// If `decodeInitFn == null`, expected to point to undefined data,
            /// which must be initialized.
            ///
            /// If `decodeInitFn != null`, expected to either have been initialized
            /// by `decodeInitFn`, or otherwise to be conformant with the documented
            /// expectations of the implementation. Consult with the documentation
            /// of the implementation to learn about the state of `value.*` in the
            /// case of an error during `decode`.
            value: *V,
            /// Must point to a value of type `DecodeCtx`.
            ctx_ptr: *const anyopaque,
        ) DecodeReaderError!void,

        /// Frees any of the resources held by `value.*`.
        /// Assumes `value.*` is in a valid state as defined by the implementation,
        /// meaning it must be able to free any value produced by `decodeInitFn` and `decodeFn`.
        /// If this is null, the `free` method is a noop, meaning the implementation does not
        /// need to free any resources.
        freeFn: ?fn (
            gpa_opt: ?std.mem.Allocator,
            value: *const V,
            /// Must point to a value of type `DecodeCtx`.
            ctx_ptr: *const anyopaque,
        ) void,
        const CodecSelf = @This();

        /// Encodes `value.*` to the `writer` stream.
        pub fn encode(
            self: CodecSelf,
            writer: *std.Io.Writer,
            config: Config,
            value: *const V,
            ctx: self.EncodeCtx,
        ) EncodeWriterError!void {
            return self.encodeFn(writer, config, value, @ptrCast(&ctx));
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
        ) EncodeWriterError!usize {
            var fixed_writer: std.Io.Writer = .fixed(slice);
            try self.encode(&fixed_writer, config, value, ctx);
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
        /// If the codec requires allocation, `gpa_opt` must be non-null.
        pub fn decode(
            self: CodecSelf,
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            ctx: self.DecodeCtx,
        ) DecodeReaderError!V {
            var value: V = undefined;
            try self.decodeInitOne(gpa_opt, &value, ctx);
            errdefer if (self.decodeInitFn != null) {
                self.free(gpa_opt, &value, ctx);
            };

            try self.decodeInto(reader, gpa_opt, config, &value, ctx);
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
        ) DecodeSliceError!struct { V, usize } {
            const decode_init_defined = self.decodeInitFn != null;

            var value: V = undefined;
            try self.decodeInitOne(gpa_opt, &value, ctx);
            errdefer if (decode_init_defined) self.free(gpa_opt, &value, ctx);

            const len = try self.decodeSliceInto(src, gpa_opt, config, &value, ctx);
            errdefer if (!decode_init_defined) self.free(gpa_opt, &value, ctx);

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
        ) (DecodeSliceError || error{Overlong})!V {
            const value, const len = try self.decodeSlice(src, gpa_opt, config, ctx);
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
        ) DecodeSliceError!V {
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
        /// If the codec requires allocation for decodeInit, `gpa_opt` must be non-null.
        pub fn decodeInitMany(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            values: []V,
            ctx: self.DecodeCtx,
        ) std.mem.Allocator.Error!void {
            const decodeInitFn = self.decodeInitFn orelse return;
            return try decodeInitFn(gpa_opt, values, @ptrCast(&ctx));
        }

        /// Decodes into `value.*` from the `reader` stream.
        /// If the codec requires allocation, `gpa_opt` must be non-null.
        /// Caller is responsible for freeing any resources held by `value.*`,
        /// including in event of failure.
        ///
        /// See doc comment on `decodeInitFn` for commentary on the expected
        /// initial state of `value.*`.
        pub fn decodeInto(
            self: CodecSelf,
            reader: *std.Io.Reader,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            value: *V,
            ctx: self.DecodeCtx,
        ) DecodeReaderError!void {
            return self.decodeFn(reader, gpa_opt, config, value, @ptrCast(&ctx));
        }

        /// Same as `decodeInto`, but takes a slice directly as input.
        /// Returns the number of bytes in `src` which were consumed to decode into `value.*`.
        pub fn decodeSliceInto(
            self: CodecSelf,
            src: []const u8,
            gpa_opt: ?std.mem.Allocator,
            config: Config,
            value: *V,
            ctx: self.DecodeCtx,
        ) DecodeSliceError!usize {
            var reader: std.Io.Reader = .fixed(src);
            self.decodeInto(&reader, gpa_opt, config, value, ctx) catch |err| switch (err) {
                error.DecodeFailed => |e| return e,
                error.OutOfMemory => |e| return e,
                error.EndOfStream => |e| return e,
                error.ReadFailed => unreachable, // fixed-buffer reader cannot fail, it only returns error.EndOfStream.
            };
            return reader.seek;
        }

        /// Frees any of the resources held by `value.*`.
        /// Expects `value.*` to be in a valid state as defined by the implementation.
        /// Does not free the `value` as a pointer.
        /// If the codec requires allocation, `gpa_opt` must be non-null.
        pub fn free(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            value: *const V,
            ctx: self.DecodeCtx,
        ) void {
            const freeFn = self.freeFn orelse return;
            return freeFn(
                gpa_opt,
                value,
                @ptrCast(&ctx),
            );
        }

        /// Construct a codec from a composition of standard codecs for an assortment of types,
        /// defined to behave in line with the bincode specification.
        pub fn standard(constructor: StdCodec(V)) CodecSelf {
            return constructor.codec;
        }

        // -- Helpers for safely implementing common codecs -- //

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, config: Config, gpa_opt: ?std.mem.Allocator, value: *const V, ctx: EncodeCtx) EncodeWriterError!void { ... }
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

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = if (@TypeOf(methods.decodeInit) != @TypeOf(null)) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (@TypeOf(methods.free) != @TypeOf(null)) erased.free else null,
            };
        }

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, config: Config, gpa_opt: ?std.mem.Allocator, value: *const V, ctx: EncodeCtx) EncodeWriterError!void { ... }
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
                    value: *const V,
                    ctx_ptr: *const anyopaque,
                ) EncodeWriterError!void {
                    const ctx: *const EncodeCtx = @ptrCast(@alignCast(ctx_ptr));
                    try methods.encode(writer, config, value, ctx.*);
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx_ptr: *const anyopaque,
                ) std.mem.Allocator.Error!void {
                    const ctx: *const DecodeCtx = @ptrCast(@alignCast(ctx_ptr));
                    try methods.decodeInit(gpa_opt, values, ctx.*);
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    gpa_opt: ?std.mem.Allocator,
                    config: Config,
                    value: *V,
                    ctx_ptr: *const anyopaque,
                ) DecodeReaderError!void {
                    const ctx: *const DecodeCtx = @ptrCast(@alignCast(ctx_ptr));
                    try methods.decode(reader, config, gpa_opt, value, ctx.*);
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx_ptr: *const anyopaque,
                ) void {
                    const ctx: *const DecodeCtx = @ptrCast(@alignCast(ctx_ptr));
                    methods.free(gpa_opt, value, ctx.*);
                }
            };
        }
    };
}

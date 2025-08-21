const std = @import("std");

pub const varint = @import("varint.zig");

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
/// Includes an optional type field for specifying additional runtime context if necessary.
pub fn Codec(comptime V: type) type {
    if (V == noreturn) unreachable;
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
            var list: std.ArrayListUnmanaged(u8) = .empty;
            defer list.deinit(gpa);
            try self.encodeToArrayList(gpa, &list, config, value, ctx);
            return try list.toOwnedSlice(gpa);
        }

        /// Encodes `value.*`, appending the encoded representation to `list`, growing it with `gpa`.
        /// Conveniently translates `error.WriteFailed` into `error.OutOfMemory`.
        pub fn encodeToArrayList(
            self: CodecSelf,
            gpa: std.mem.Allocator,
            list: *std.ArrayListUnmanaged(u8),
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

        // -- Standard Codecs -- //

        /// Standard codec for a zero-sized value.
        /// Never fails to encode or decode.
        pub const std_void: CodecSelf = .implement(void, void, struct {
            comptime {
                if (@sizeOf(V) != 0) @compileError(
                    "void codec is not implemented for type " ++ @typeName(V) ++
                        " of size " ++ std.fmt.comptimePrint("{d}", .{@sizeOf(V)}),
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: Config,
                value: *const V,
                ctx: void,
            ) EncodeWriterError!void {
                _ = ctx;
                _ = writer;
                _ = config;
                _ = value;
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                gpa_opt: ?std.mem.Allocator,
                value: *V,
                ctx: void,
            ) DecodeReaderError!void {
                _ = ctx;
                _ = reader;
                _ = config;
                _ = value;
                _ = gpa_opt;
            }

            pub const free = null;
        });

        /// Standard codec for a byte.
        /// Never fails to encode or decode.
        pub const std_byte: Codec(u8) = .implement(void, void, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                _: Config,
                value: *const u8,
                _: void,
            ) EncodeWriterError!void {
                try writer.writeByte(value.*);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: Config,
                _: ?std.mem.Allocator,
                value: *u8,
                _: void,
            ) DecodeReaderError!void {
                try reader.readSliceAll(value[0..1]);
            }

            pub const free = null;
        });

        pub const StdBoolDecodeDiag = struct {
            /// Value of the actual decoded byte with an erroneous value.
            /// Only set value when `error.DecodeFailed` is returned.
            real_byte: ?u8,

            pub const init: StdBoolDecodeDiag = .{ .real_byte = null };
        };

        /// Standard codec for a boolean.
        /// Never fails to encode.
        /// Failure to decode indicates a byte value other than 0 or 1.
        /// Decode's initial state is write-only.
        pub const std_bool: Codec(bool) = .implement(void, ?*StdBoolDecodeDiag, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                _: Config,
                value: *const bool,
                _: void,
            ) EncodeWriterError!void {
                try writer.writeByte(@intFromBool(value.*));
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: Config,
                _: ?std.mem.Allocator,
                value: *bool,
                maybe_diag: ?*StdBoolDecodeDiag,
            ) DecodeReaderError!void {
                var real_byte: u8 = undefined;
                try reader.readSliceAll((&real_byte)[0..1]);
                value.* = switch (real_byte) {
                    0 => false,
                    1 => true,
                    else => {
                        if (maybe_diag) |diag| diag.real_byte = real_byte;
                        return error.DecodeFailed;
                    },
                };
            }

            pub const free = null;
        });

        /// Standard codec for an integer. Encodes `usize` and `isize` as `u64` and `i64`, respectively.
        /// Never fails to encode.
        /// Failure to decode indicates that the value overflowed.
        /// Decode's initial state is write-only.
        pub const std_int: CodecSelf = .implement(void, void, struct {
            const signedness = @typeInfo(V).int.signedness;
            const Int = blk: {
                switch (V) {
                    usize => break :blk u64,
                    isize => break :blk i64,
                    else => {},
                }

                const encoded_bits = switch (@typeInfo(V).int.bits) {
                    0 => @compileError("This codec does not support zero-sized types."),
                    (0 + 1)...8 => @compileError("This codec does not support byte-sized types."),
                    (8 + 1)...16 => 16,
                    (16 + 1)...32 => 32,
                    (32 + 1)...64 => 64,
                    (64 + 1)...128 => 128,
                    (128 + 1)...256 => 256,
                    else => @compileError("This codec does not support integers of type " ++ @typeName(V)),
                };

                break :blk std.meta.Int(signedness, encoded_bits);
            };

            pub fn encode(
                writer: *std.Io.Writer,
                config: Config,
                value: *const V,
                _: void,
            ) EncodeWriterError!void {
                switch (config.int) {
                    .fixint => {
                        try writer.writeInt(V, value.*, config.endian);
                    },
                    .varint => {
                        const unsigned_int = switch (signedness) {
                            .signed => varint.zigzag.signedToUnsigned(Int, value.*),
                            .unsigned => value.*,
                        };
                        var buffer: [varint.IntKind.fullEncodedLen(.maximum)]u8 = undefined;
                        const int_kind = varint.encode(unsigned_int, &buffer, config.endian);
                        try writer.writeAll(buffer[0..int_kind.fullEncodedLen()]);
                    },
                }
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                _: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) DecodeReaderError!void {
                switch (config.int) {
                    .fixint => {
                        var int_bytes: [@sizeOf(Int)]u8 = undefined;
                        try reader.readSliceAll(&int_bytes);
                        const int = std.mem.readInt(Int, &int_bytes, config.endian);
                        if (int > std.math.maxInt(V)) return error.DecodeFailed;
                        value.* = @intCast(int);
                    },
                    .varint => {
                        const raw_int = try varint.decodeReader(reader, config.endian);
                        switch (signedness) {
                            .signed => {
                                const EncodedInt = varint.zigzag.SignedAsUnsigned(Int);
                                if (raw_int > std.math.maxInt(EncodedInt)) return error.DecodeFailed;
                                const encoded_int: EncodedInt = @intCast(raw_int);
                                const int: Int = varint.zigzag.signedFromUnsigned(Int, encoded_int);
                                if (int > std.math.maxInt(V)) return error.DecodeFailed;
                                value.* = @intCast(int);
                            },
                            .unsigned => {
                                if (raw_int > std.math.maxInt(V)) return error.DecodeFailed;
                                value.* = @intCast(raw_int);
                            },
                        }
                    },
                }
            }

            pub const free = null;
        });

        /// Standard codec for a float.
        /// Never fails to encode or decode.
        /// Decode's initial state is write-only.
        pub const std_float: CodecSelf = .implement(void, void, struct {
            const AsInt = std.meta.Int(.unsigned, @bitSizeOf(V));
            comptime {
                switch (V) {
                    f32, f64 => {},
                    else => @compileError("float codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: Config,
                value: *const V,
                _: void,
            ) EncodeWriterError!void {
                const as_int_endian = std.mem.nativeTo(AsInt, @bitCast(value.*), config.endian);
                try writer.writeAll(@ptrCast(&as_int_endian));
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                _: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) DecodeReaderError!void {
                try reader.readSliceAll(@ptrCast(value));
                value.* = @bitCast(std.mem.nativeTo(AsInt, @bitCast(value.*), config.endian));
            }

            pub const free = null;
        });

        /// Standard codec for a UTF-8 codepoint.
        /// Failure to encode indicates an invalid codepoint value.
        /// Failure to decode indicates an invalid codepoint value.
        /// Decode's initial state is write-only.
        pub const std_utf8_codepoint: CodecSelf = .implement(void, void, struct {
            comptime {
                switch (V) {
                    u1, u2, u3, u4, u5, u6, u7 => {},
                    u8, u16, u21, u32 => {},
                    else => @compileError("char codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(
                writer: *std.Io.Writer,
                _: Config,
                value: *const V,
                _: void,
            ) EncodeWriterError!void {
                if (value.* > std.math.maxInt(u21)) {
                    return error.EncodeFailed;
                }
                const cp_val: u21 = @intCast(value.*);
                const cp_len = std.unicode.utf8CodepointSequenceLength(cp_val) catch
                    return error.EncodeFailed;
                var encoded_buffer: [4]u8 = undefined;
                const encoded = encoded_buffer[0..cp_len];
                const actual_cp_len = std.unicode.utf8Encode(cp_val, encoded) catch
                    return error.EncodeFailed;
                std.debug.assert(cp_len == actual_cp_len);
                try writer.writeAll(encoded);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: Config,
                _: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) DecodeReaderError!void {
                const first_byte = first_byte: {
                    var first_byte: u8 = undefined;
                    try reader.readSliceAll((&first_byte)[0..1]);
                    break :first_byte first_byte;
                };
                const cp_len = std.unicode.utf8ByteSequenceLength(first_byte) catch return error.DecodeFailed;
                var encoded_buffer: [4]u8 = undefined;
                const encoded = encoded_buffer[0..cp_len];
                encoded[0] = first_byte;
                if (cp_len != 1) try reader.readSliceAll(encoded[1..]);
                const cp = switch (cp_len) {
                    1 => encoded[0],
                    2 => std.unicode.utf8Decode2(encoded[0..2].*),
                    3 => std.unicode.utf8Decode3(encoded[0..3].*),
                    4 => std.unicode.utf8Decode4(encoded[0..4].*),
                    else => unreachable,
                } catch return error.DecodeFailed;
                if (cp > std.math.maxInt(V)) {
                    return error.DecodeFailed;
                }
                value.* = @intCast(cp);
            }

            pub const free = null;
        });

        pub fn StdOptionalDecodeCtx(comptime PayloadCtx: type) type {
            return struct {
                diag: ?*StdBoolDecodeDiag,
                pl: PayloadCtx,
            };
        }

        /// Standard codec for an optional.
        /// Allocation requirement defined by `payload_codec`.
        /// Never fails to encode the null bool, payload fallability is defined by `payload_codec`.
        /// Failure to decode indicates either a failure to decode the boolean, or the potential payload.
        /// When `payload_codec.decodeInitFn != null`, decode's initial state is null. If it is non-null,
        /// the existing payload must conform to `payload_codec`'s expectations; if the decoded value is
        /// null, the `payload_codec` will be used to free the existing payload.
        /// Otherwise, when `payload_codec.decodeInitFn == null`, decode's initial state is write-only.
        pub fn stdOptional(payload_codec: Codec(Child)) CodecSelf {
            const EncodeCtx = payload_codec.EncodeCtx;
            const DecodeCtx = StdOptionalDecodeCtx(payload_codec.DecodeCtx);

            const decode_ctx_opt = switch (@typeInfo(payload_codec.DecodeCtx)) {
                .void, .optional => true,
                else => false,
            };
            const DecodeCtxParam = if (decode_ctx_opt) ?DecodeCtx else DecodeCtx;

            const erased = ImplementMethods(EncodeCtx, DecodeCtxParam, struct {
                const Unwrapped = @typeInfo(V).optional.child;

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                    ctx: EncodeCtx,
                ) EncodeWriterError!void {
                    std_bool.encode(writer, config, &(value.* != null), ctx) catch |err| switch (err) {
                        error.WriteFailed => |e| return e,
                        error.EncodeFailed => unreachable, // bool never fails to encode
                    };
                    const payload = if (value.*) |*unwrapped| unwrapped else return;
                    try payload_codec.encode(writer, config, payload, {});
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    _: DecodeCtxParam,
                ) std.mem.Allocator.Error!void {
                    _ = gpa_opt;
                    @memset(values, null);
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    maybe_ctx: DecodeCtxParam,
                ) DecodeReaderError!void {
                    const ctx: DecodeCtx = ctx: {
                        if (!decode_ctx_opt) break :ctx maybe_ctx;
                        break :ctx maybe_ctx orelse .{
                            .diag = null,
                            .pl = if (payload_codec.DecodeCtx != void) null,
                        };
                    };
                    const is_some = try std_bool.decode(reader, null, config, ctx.diag);
                    if (is_some) {
                        if (payload_codec.decodeInitFn == null or value.* == null) {
                            value.* = @as(Unwrapped, undefined);
                            try payload_codec.decodeInitOne(gpa_opt, &value.*.?, ctx.pl);
                        }
                        try payload_codec.decodeInto(reader, gpa_opt, config, &value.*.?, ctx.pl);
                    } else {
                        if (payload_codec.decodeInitFn != null) if (value.*) |*pl| {
                            payload_codec.free(gpa_opt, pl, ctx.pl);
                        };
                        value.* = null;
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtxParam,
                ) void {
                    const unwrapped = if (value.*) |*unwrapped| unwrapped else return;
                    payload_codec.free(ctx.pl, gpa_opt, unwrapped);
                }
            });

            return .{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = if (payload_codec.decodeInitFn != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (payload_codec.freeFn != null) erased.free else null,
            };
        }

        pub fn StdStructEncodeCtx(field_codecs: Fields) type {
            const EncodeCtx, _ = FieldContexts(field_codecs);
            return EncodeCtx;
        }

        pub fn StdStructDecodeCtx(field_codecs: Fields) type {
            _, const DecodeCtx = FieldContexts(field_codecs);
            return DecodeCtx;
        }

        /// Standard codec for a struct.
        /// Allocation requirement defined by whether any codec in field codecs requires allocation.
        /// Failure to encode and decode defined by all of the field codecs in sequence.
        /// Decode's initial state is defined for each field based on the respective codec.
        pub fn stdStruct(field_codecs: Fields) CodecSelf {
            const s_fields = @typeInfo(V).@"struct".fields;
            const EncodeCtx, const DecodeCtx = FieldContexts(field_codecs);

            const any_decode_init, const any_free = blk: {
                @setEvalBranchQuota(s_fields.len + 2);

                var any_decode_init = false;
                var any_free = false;
                for (s_fields) |s_field| {
                    const field_codec: *const Codec(s_field.type) = @field(field_codecs, s_field.name);

                    // zig fmt: off
                    any_decode_init = any_decode_init or field_codec.decodeInitFn != null;
                    any_free        = any_free        or field_codec.freeFn       != null;
                    // zig fmt: on

                    if (any_decode_init and any_free) break;
                }

                break :blk .{ any_decode_init, any_free };
            };

            const erased = ImplementMethods(EncodeCtx, DecodeCtx, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                    ctx: EncodeCtx,
                ) EncodeWriterError!void {
                    inline for (s_fields) |s_field| {
                        const field_codec: *const Codec(s_field.type) = @field(field_codecs, s_field.name);
                        const field_ctx = if (EncodeCtx != void) blk: {
                            const pl_ctx = if (@typeInfo(EncodeCtx) != .optional) ctx else ctx orelse
                                break :blk if (field_codec.EncodeCtx != void) null;
                            break :blk @field(pl_ctx, s_field.name);
                        };
                        const field_ptr = &@field(value, s_field.name);
                        try field_codec.encode(writer, config, field_ptr, field_ctx);
                    }
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    comptime if (!any_decode_init) unreachable;
                    for (values, 0..) |*value, value_i| {
                        errdefer for (values[0..value_i]) |*prev| {
                            freeFieldSubset(s_fields.len, ctx, gpa_opt, prev);
                        };

                        inline for (s_fields, 0..) |s_field, s_field_i| {
                            errdefer freeFieldSubset(s_field_i, ctx, gpa_opt, value);
                            const field_codec: Codec(s_field.type) = @field(field_codecs, s_field.name);
                            const field_ctx = if (DecodeCtx != void) blk: {
                                const pl_ctx = if (@typeInfo(DecodeCtx) != .optional) ctx else ctx orelse
                                    break :blk if (field_codec.DecodeCtx != void) null;
                                break :blk @field(pl_ctx, s_field.name);
                            };
                            const field_ptr = &@field(value, s_field.name);
                            try field_codec.decodeInitOne(field_ctx, gpa_opt, field_ptr);
                        }
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    ctx: DecodeCtx,
                ) DecodeReaderError!void {
                    inline for (s_fields, 0..) |s_field, i| {
                        errdefer freeFieldSubset(i, gpa_opt, value, ctx);
                        const field_codec: *const Codec(s_field.type) = @field(field_codecs, s_field.name);

                        const field_ctx = if (DecodeCtx != void) blk: {
                            const pl_ctx = if (@typeInfo(DecodeCtx) != .optional) ctx else ctx orelse
                                break :blk if (field_codec.DecodeCtx != void) null;
                            break :blk @field(pl_ctx, s_field.name);
                        };

                        const field_ptr = &@field(value, s_field.name);
                        try field_codec.decodeInto(reader, gpa_opt, config, field_ptr, field_ctx);
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtx,
                ) void {
                    comptime if (!any_free) unreachable;
                    freeFieldSubset(s_fields.len, gpa_opt, value, ctx);
                }

                fn freeFieldSubset(
                    comptime n_fields_to_deinit: usize,
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtx,
                ) void {
                    inline for (s_fields[0..n_fields_to_deinit]) |s_field| {
                        const field_codec: *const Codec(s_field.type) = @field(field_codecs, s_field.name);
                        const field_ctx = if (DecodeCtx != void) blk: {
                            const pl_ctx = if (@typeInfo(DecodeCtx) != .optional) ctx else ctx orelse
                                break :blk if (field_codec.DecodeCtx != void) null;
                            break :blk @field(pl_ctx, s_field.name);
                        };
                        const field_ptr = &@field(value, s_field.name);
                        field_codec.free(gpa_opt, field_ptr, field_ctx);
                    }
                }
            });

            return .{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = if (any_decode_init) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (any_free) erased.free else null,
            };
        }

        pub const StdUnionEncodeCtx = StdStructEncodeCtx;

        pub fn StdUnionDecodeCtx(payload_codecs: Fields) type {
            _, const PayloadDecodeCtx = FieldContexts(payload_codecs);
            return struct {
                diag: ?*Codec(Tag).StdDiscriminantDecodeCtx,
                pl: PayloadDecodeCtx,

                const Tag = @typeInfo(V).@"union".tag_type.?;
            };
        }

        /// Standard codec for a tagged union, aka "enums" in the
        /// bincode specification, written in the context of rust.
        /// Allocation requirement defined by whether any codec in payload codecs requires allocation.
        /// Never fails to encode the discriminant, payload fallability is defined by `payload_codecs`.
        /// Failure to decode indicates either a failure to decode discriminant, or the potential payload.
        /// Decode's initial state is write-only, unless `decode_init_tag_opt` is specified; see that parameter's
        /// doc comment. Whether the payload's initial state is write-only or not depends on the payload
        /// codec of the specified tag.
        ///
        /// Also see:
        /// * `std_discriminant`.
        /// * `StdUnionEncodeCtx`.
        /// * `StdUnionDecodeCtx`.
        pub fn stdUnion(
            /// If non-null, specifies the tag that `decodeInit` should initialize a value
            /// to, permitting `decode` to assume the `value` pointer is valid and initialized,
            /// and can be decoded into in-place, with the semantics of doing so for each variant
            /// being defined by the respective codec in `payload_codecs`.
            /// It should also be noted that under this configuration, if the decoded TODO
            ///
            /// If null, decode's initial state is write-only, since it cannot be assumed
            /// that the union is properly initialized.
            comptime decode_init_tag_opt: ?@typeInfo(V).@"union".tag_type.?,
            payload_codecs: Fields,
        ) CodecSelf {
            const union_info = @typeInfo(V).@"union";
            const Tag = union_info.tag_type.?;
            const EncodeCtx = StdUnionEncodeCtx(payload_codecs);
            const DecodeCtx = StdUnionDecodeCtx(payload_codecs);

            @setEvalBranchQuota(union_info.fields.len);
            const any_free = for (union_info.fields) |u_field| {
                const payload_codec: *const Codec(u_field.type) = @field(payload_codecs, u_field.name);
                if (payload_codec.freeFn != null) break true;
            } else false;

            const erased = ImplementMethods(EncodeCtx, DecodeCtx, struct {
                const StdUnionImpl = @This();
                const tag_codec: Codec(Tag) = .std_discriminant;

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                    maybe_ctx: EncodeCtx,
                ) EncodeWriterError!void {
                    const tag: union_info.tag_type.? = value.*;
                    try tag_codec.encode(writer, config, &tag, {});
                    switch (value.*) {
                        inline else => |*payload_ptr, itag| {
                            const Payload = @TypeOf(payload_ptr.*);
                            const payload_codec: *const Codec(Payload) = @field(payload_codecs, @tagName(itag));

                            const payload_ctx: payload_codec.EncodeCtx = ctx: {
                                const ctx = switch (@typeInfo(payload_codec.EncodeCtx)) {
                                    .void => break :ctx {},
                                    .optional => maybe_ctx orelse break :ctx null,
                                    else => maybe_ctx,
                                };
                                break :ctx @field(ctx, @tagName(itag));
                            };

                            try payload_codec.encode(writer, config, payload_ptr, payload_ctx);
                        },
                    }
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    const decode_init_tag = comptime decode_init_tag_opt.?;

                    const Payload = @FieldType(V, @tagName(decode_init_tag));
                    const payload_codec: *const Codec(Payload) = @field(payload_codecs, @tagName(decode_init_tag));

                    const payload_ctx: payload_codec.DecodeCtx = ctx: {
                        const pl_ctx_union = switch (@typeInfo(payload_codec.DecodeCtx)) {
                            .void => break :ctx {},
                            .optional => ctx.pl orelse break :ctx null,
                            else => ctx.pl,
                        };
                        break :ctx @field(pl_ctx_union, @tagName(decode_init_tag));
                    };

                    @memset(values, comptime @unionInit(V, @tagName(decode_init_tag), undefined));
                    if (comptime payload_codec.decodeInitFn != null) {
                        for (values, 0..) |*u, i| {
                            errdefer for (values[0..i]) |*prev| {
                                const prev_pl = &@field(prev, @tagName(decode_init_tag));
                                payload_codec.free(prev_pl);
                            };
                            const pl = &@field(u, @tagName(decode_init_tag));
                            try payload_codec.decodeInitOne(payload_ctx, gpa_opt, pl);
                        }
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    ctx: DecodeCtx,
                ) DecodeReaderError!void {
                    const valid_init_state = comptime decode_init_tag_opt != null;
                    switch (try tag_codec.decode(reader, null, config, ctx.diag)) {
                        inline else => |decoded_tag| {
                            const Payload = @FieldType(V, @tagName(decoded_tag));
                            const payload_codec: *const Codec(Payload) = @field(payload_codecs, @tagName(decoded_tag));

                            const payload_ctx: payload_codec.DecodeCtx = ctx: {
                                const pl_ctx_union = switch (@typeInfo(payload_codec.DecodeCtx)) {
                                    .void => break :ctx {},
                                    .optional => ctx.pl orelse break :ctx null,
                                    else => ctx.pl,
                                };
                                break :ctx @field(pl_ctx_union, @tagName(decoded_tag));
                            };

                            // if there's no valid inital state to worry about, just ovewrite and decode
                            if (!valid_init_state) {
                                value.* = @unionInit(V, @tagName(decoded_tag), undefined);
                                const payload_ptr = &@field(value, @tagName(decoded_tag));
                                try payload_codec.decodeInitOne(gpa_opt, payload_ptr, payload_ctx);

                                // if there's a valid initial state and it matches the decoded tag, decode the payload in-place.
                            } else if (value.* != decoded_tag) {
                                // otherwise, initialize the new payload, free the old one, set the new payload, and then decode into it.
                                var payload: @FieldType(V, @tagName(decoded_tag)) = undefined;
                                try payload_codec.decodeInitOne(gpa_opt, &payload, payload_ctx);
                                if (any_free) StdUnionImpl.free(gpa_opt, value, ctx);
                                value.* = @unionInit(V, @tagName(decoded_tag), payload);
                            }

                            const payload_ptr = &@field(value, @tagName(decoded_tag));
                            try payload_codec.decodeInto(reader, gpa_opt, config, payload_ptr, payload_ctx);
                        },
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtx,
                ) void {
                    comptime if (!any_free) unreachable;
                    switch (value.*) {
                        inline else => |*payload_ptr, itag| {
                            const Payload = @FieldType(V, @tagName(itag));
                            const payload_codec: *const Codec(Payload) = @field(payload_codecs, @tagName(itag));

                            const payload_ctx: payload_codec.DecodeCtx = ctx: {
                                const pl_ctx_union = switch (@typeInfo(payload_codec.DecodeCtx)) {
                                    .void => break :ctx {},
                                    .optional => ctx.pl orelse break :ctx null,
                                    else => ctx.pl,
                                };
                                break :ctx @field(pl_ctx_union, @tagName(itag));
                            };

                            payload_codec.free(gpa_opt, payload_ptr, payload_ctx);
                        },
                    }
                }
            });

            return .{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = if (decode_init_tag_opt != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (any_free) erased.free else null,
            };
        }

        pub const StdDiscriminantDecodeCtx = struct {
            /// Value of the actual decoded u32 with an erroneous value.
            /// Only set if when `error.DecodeFailed` is returned.
            real_int: ?u32,

            pub const init: StdBoolDecodeDiag = .{ .real_int = null };
        };

        /// Standard codec for an enum used as a discriminant,
        /// aka the tag of a tagged union, aka the tag of a rust enum.
        /// Failure to decode indicates the value overflowed or didn't match a valid value.
        /// Decode's initial state is write-only.
        pub const std_discriminant: CodecSelf = .implement(void, ?*StdDiscriminantDecodeCtx, struct {
            const enum_info = @typeInfo(V).@"enum";
            const tag_info = @typeInfo(enum_info.tag_type).int;
            comptime {
                const err_msg_preamble = "discriminant codec is not implemented for enum " ++ @typeName(V);
                const err_msg_preamble_bad_int = " with tag type " ++ @typeName(enum_info.tag_type);
                if (tag_info.signedness != .unsigned) @compileError(
                    err_msg_preamble ++ err_msg_preamble_bad_int ++ ", which isn't unsigned.",
                );
                if (tag_info.bits > 32) @compileError(
                    err_msg_preamble ++ err_msg_preamble_bad_int ++ ", which has more than 32 bits.",
                );
                if (!enum_info.is_exhaustive) @compileError(
                    err_msg_preamble ++ ", which is non-exhaustive.",
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: Config,
                value: *const V,
                _: void,
            ) EncodeWriterError!void {
                const as_u32: u32 = @intFromEnum(value.*);
                return Codec(u32).std_int.encode(writer, config, &as_u32, {});
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                _: ?std.mem.Allocator,
                value: *V,
                maybe_diag: ?*StdDiscriminantDecodeCtx,
            ) DecodeReaderError!void {
                const as_u32 = try Codec(u32).std_int.decode(reader, null, config, {});
                if (as_u32 > std.math.maxInt(enum_info.tag_type)) {
                    if (maybe_diag) |diag| diag.real_int = as_u32;
                    return error.DecodeFailed;
                }
                const raw: enum_info.tag_type = @intCast(as_u32);
                // TODO: if/when https://github.com/ziglang/zig/issues/12250 is implemented, replace this `enums.fromInt` with an
                // implementation that leverages where we create an enum with all the same type info as `V`, but with `.is_exhaustive = false`,
                // such that we could cast `raw` to that non-exhaustive equivalent, and switch on that value like so:
                // ```
                // const NonExhaustive = ;
                // const non_exhaustive: NonExhaustive = @enumFromInt(raw);
                // return switch (non_exhaustive) {
                //     _ => return error.DecodeFailed,
                //     else => |tag| @enumFromInt(@intFromEnum(tag)),
                // };
                // ```
                value.* = std.enums.fromInt(V, raw) orelse {
                    if (maybe_diag) |diag| diag.real_int = as_u32;
                    return error.DecodeFailed;
                };
            }

            pub const free = null;
        });

        /// Standard codec for a byte array. Encodes no length.
        /// Optimization over `stdArray(&.std_byte)`.
        /// Decode's initial state is write-only.
        pub const std_byte_array: CodecSelf = .implement(void, void, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                _: Config,
                value: *const V,
                _: void,
            ) EncodeWriterError!void {
                try writer.writeAll(value);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: Config,
                _: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) DecodeReaderError!void {
                try reader.readSliceAll(value);
            }

            pub const free = null;
        });

        /// Standard codec for an array. Encodes no length.
        /// Allocation requirement defined by element codec.
        /// Decode's initial state is defined as an array of initial states conforming to `element_codec`'s expectations.
        /// Also see `std_byte_array`.
        pub fn stdArray(element_codec: Codec(Element)) CodecSelf {
            const erased = ImplementMethods(void, void, struct {
                const not_implemented_err_msg = "array codec not is not implemented for type " ++ @typeName(V);

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                    _: void,
                ) EncodeWriterError!void {
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| try element_codec.encode(writer, config, elem, {}),
                        .vector => |vec_info| for (0..vec_info.len) |i| try element_codec.encode(writer, config, &value[i], {}),
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    _: void,
                ) std.mem.Allocator.Error!void {
                    switch (@typeInfo(V)) {
                        .array => try element_codec.decodeInitMany(gpa_opt, @ptrCast(values)), // flatten `[][n]E` as `[]E`.
                        .vector => |vec_info| for (values) |*value| {
                            var arr: [vec_info.len]Element = value.*;
                            try element_codec.decodeInitMany(gpa_opt, &arr);
                            value.* = arr;
                        },
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    _: void,
                ) DecodeReaderError!void {
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| try element_codec.decodeInto(reader, gpa_opt, config, elem, {}),
                        .vector => |vec_info| for (0..vec_info.len) |i| try element_codec.decodeInto(reader, gpa_opt, config, &value[i], {}),
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V, _: void) void {
                    if (element_codec.freeFn == null) return;
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| element_codec.free(gpa_opt, elem),
                        .vector => |vec_info| for (0..vec_info.len) |i| element_codec.free(gpa_opt, &value[i]),
                        else => @compileError(not_implemented_err_msg),
                    }
                }
            });

            return .{
                .EncodeCtx = void,
                .encodeFn = erased.encode,

                .DecodeCtx = void,
                .decodeInitFn = if (element_codec.decodeInitFn != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (element_codec.freeFn != null) erased.free else null,
            };
        }

        /// Standard codec for a byte slice. Encodes the length. Optimization over `stdSlice(&.std_byte)`.
        /// Requires allocation.
        ///
        /// Decode's initial state is `&.{}`. If it is non-empty, it must have been allocated using
        /// the supplied `gpa_opt.?`; it will be resized to the decoded length if necessary, and the
        /// contents will be overwritten with the contents read from the stream - the pointed-to bytes
        /// are assumed to be write-only during the duration of the function.
        /// Allocation failure while doing so may result in destruction of the original allocation,
        /// setting it to empty.
        pub const std_byte_slice: CodecSelf = .implement(void, void, struct {
            const ptr_info = @typeInfo(V).pointer;
            comptime {
                if (ptr_info.size != .slice) @compileError(
                    "single item ptr codec is not implemented for type " ++ @typeName(V),
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: Config,
                value: *const V,
                _: void,
            ) EncodeWriterError!void {
                try Codec(usize).std_int.encode(writer, config, &value.len, {});
                try writer.writeAll(value.*);
            }

            pub fn decodeInit(
                gpa_opt: ?std.mem.Allocator,
                values: []V,
                _: void,
            ) std.mem.Allocator.Error!void {
                _ = gpa_opt.?;
                @memset(values, &.{});
            }

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                gpa_opt: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) DecodeReaderError!void {
                const gpa = gpa_opt.?;

                const len = try Codec(usize).std_int.decode(reader, null, config, {});
                if (value.len != len) blk: {
                    const old_slice_mut = @constCast(value.*); // assumes this is allocated data, which must be mutable.
                    if (gpa.resize(old_slice_mut, len)) {
                        value.len = len;
                        break :blk;
                    }
                    if (gpa.remap(old_slice_mut, len)) |new_slice| {
                        value.* = new_slice;
                        break :blk;
                    }
                    gpa.free(value.*);
                    value.* = &.{};
                    value.* = try gpa.alignedAlloc(u8, .fromByteUnits(ptr_info.alignment), len);
                }

                try reader.readSliceAll(@constCast(value.*)); // assumes this is allocated data, which must be mutable.
            }

            pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V, _: void) void {
                const gpa = gpa_opt.?;
                gpa.free(value.*);
            }
        });

        /// Standard codec for a slice. Encodes the length.
        /// Requires allocation, for the slice, and possibly for the elements (based on element codec).
        /// Also see `std_byte_array`.
        pub fn stdSlice(element_codec: Codec(Element)) CodecSelf {
            return .implement(void, void, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .slice) @compileError(
                        "single item ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                    _: void,
                ) EncodeWriterError!void {
                    try Codec(usize).std_int.encode(writer, config, &value.len, {});
                    for (value.*) |*elem| try element_codec.encode(writer, config, elem, {});
                }

                pub const decodeInit = null;

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    _: void,
                ) DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const len = try Codec(usize).std_int.decode(reader, null, config, {});
                    const slice = try gpa.alignedAlloc(ptr_info.child, .fromByteUnits(ptr_info.alignment), len);
                    errdefer gpa.free(slice);

                    for (slice, 0..) |*elem, i| {
                        errdefer if (element_codec.freeFn != null) {
                            for (slice[0..i]) |*prev| element_codec.free(gpa, prev);
                        };
                        try element_codec.decodeInto(reader, gpa, config, elem, {});
                    }
                    value.* = slice;
                }

                pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V, _: void) void {
                    const gpa = gpa_opt.?;
                    if (element_codec.freeFn != null) {
                        for (value.*) |*elem| element_codec.free(gpa, elem);
                    }
                    gpa.free(value.*);
                }
            });
        }

        /// Standard codec for a byte array pointer. Encodes the length. Optimization over `stdArrayPtr(&.std_byte)`.
        /// Requires allocation.
        pub const std_byte_array_ptr: CodecSelf = .implement(void, void, struct {
            const ptr_info = @typeInfo(V).pointer;
            comptime {
                if (ptr_info.size != .one or @typeInfo(ptr_info.child) != .array) @compileError(
                    "array ptr codec is not implemented for type " ++ @typeName(V),
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: Config,
                value: *const V,
                _: void,
            ) EncodeWriterError!void {
                try Codec(usize).std_int.encode(writer, config, &value.*.len, {});
                try writer.writeAll(value.*);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                gpa_opt: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) DecodeReaderError!void {
                const gpa = gpa_opt.?;

                const expected_len = @typeInfo(ptr_info.child).array.len;
                const actual_len = try Codec(usize).std_int.decode(reader, null, config, {});
                if (actual_len != expected_len) return error.DecodeFailed;

                const slice = (try gpa.alignedAlloc(
                    u8,
                    .fromByteUnits(ptr_info.alignment),
                    actual_len,
                ))[0..expected_len];

                try reader.readSliceAll(slice);
                value.* = slice;
            }

            pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V, _: void) void {
                const gpa = gpa_opt.?;
                gpa.free(value.*);
            }
        });

        /// Standard codec for an array pointer. Encodes the length.
        /// Also see `std_byte_array_ptr`.
        /// Decoding allocates the result.
        pub fn stdArrayPtr(element_codec: Codec(Element)) CodecSelf {
            return .implement(void, void, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .one or @typeInfo(ptr_info.child) != .array) @compileError(
                        "array ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }

                fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                    _: void,
                ) EncodeWriterError!void {
                    try Codec(usize).std_int.encode(writer, config, &value.*.len, {});
                    try Codec(ptr_info.child).stdArray(element_codec).encode(writer, config, value.*, {});
                }

                pub const decodeInit = null;

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    _: void,
                ) DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const expected_len = @typeInfo(ptr_info.child).array.len;
                    const actual_len = try Codec(usize).std_int.decode(reader, null, config, {});
                    if (actual_len != expected_len) return error.DecodeFailed;

                    const slice = (try gpa.alignedAlloc(
                        @typeInfo(ptr_info.child).array.child,
                        .fromByteUnits(ptr_info.alignment),
                        actual_len,
                    ))[0..expected_len];
                    errdefer gpa.free(slice);

                    try Codec(ptr_info.child).stdArray(element_codec).decodeInto(reader, gpa, config, slice, {});
                    value.* = slice;
                }

                pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V, _: void) void {
                    const gpa = gpa_opt.?;
                    Codec(ptr_info.child).stdArray(element_codec).free(gpa, value.*, {});
                    gpa.free(value.*);
                }
            });
        }

        /// Standard codec for a single item pointer.
        /// Decoding allocates the result.
        /// Disallows `Child = [n]T` and `Child = @Vector(n, T)`, see `stdArrayPtr` instead.
        pub fn stdSingleItemPtr(child_codec: Codec(Child)) CodecSelf {
            return .implement(void, void, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .one) @compileError(
                        "single item ptr codec is not implemented for type " ++ @typeName(V),
                    );
                    if (@typeInfo(ptr_info.child) == .array or
                        @typeInfo(ptr_info.child) == .vector //
                    ) @compileError(
                        "single item ptr codec should not be used for type " ++ @typeName(V) ++
                            ", see `stdArrayPtr` instead",
                    );
                }

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                    _: void,
                ) EncodeWriterError!void {
                    try child_codec.encode(writer, config, value.*, {});
                }

                pub const decodeInit = null;

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    _: void,
                ) DecodeReaderError!void {
                    const gpa = gpa_opt.?;
                    const aligned_bytes = try gpa.alignedAlloc(
                        u8,
                        .fromByteUnits(ptr_info.alignment),
                        @sizeOf(ptr_info.child),
                    );
                    errdefer gpa.free(aligned_bytes);
                    const ptr = std.mem.bytesAsValue(
                        ptr_info.child,
                        aligned_bytes[0..@sizeOf(ptr_info.child)],
                    );
                    try child_codec.decodeInto(reader, gpa, config, ptr, {});
                    value.* = ptr;
                }

                pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V, _: void) void {
                    const gpa = gpa_opt.?;
                    child_codec.free(gpa, value.*, {});
                    gpa.destroy(value.*);
                }
            });
        }

        pub const ArrayListElem = switch (@typeInfo(V)) {
            .@"struct" => blk: {
                if (!@hasDecl(V, "Slice")) break :blk noreturn;
                if (@TypeOf(&V.Slice) != *const type) break :blk noreturn;
                const ptr_info = switch (@typeInfo(V.Slice)) {
                    .pointer => |ptr_info| ptr_info,
                    else => break :blk noreturn,
                };
                if (ptr_info.size != .slice) break :blk noreturn;
                const Expected = std.ArrayListAlignedUnmanaged(ptr_info.child, .fromByteUnits(ptr_info.alignment));
                if (V != Expected) break :blk noreturn;
                break :blk ptr_info.child;
            },
            else => noreturn,
        };

        /// Standard codec for an arraylist.
        /// Requires allocation, for the arraylist, and possibly for the elements (based on element codec).
        ///
        /// Decode's initial state is `.empty`. If it is non-empty, it must have been allocated using
        /// the supplied `gpa_opt.?`; it will be resized to the decoded length if necessary, freeing
        /// the discarded elements or initializing added elements using `element_codec`, and decoding into
        /// the existing elements, which must be in a valid initial state conforming to `element_codec`'s
        /// documented expectations.
        /// Allocation failure while doing so may result in destruction of the original allocation,
        /// setting it to empty.
        pub fn stdArrayList(element_codec: Codec(ArrayListElem)) CodecSelf {
            const alignment: std.mem.Alignment =
                .fromByteUnits(@typeInfo(V.Slice).pointer.alignment);
            const ArrayListType = std.ArrayListAlignedUnmanaged(ArrayListElem, alignment);
            return .implement(void, void, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const ArrayListType,
                    _: void,
                ) EncodeWriterError!void {
                    const std_slice_codec: Codec(ArrayListType.Slice) = .stdSlice(element_codec);
                    try std_slice_codec.encode(writer, config, &value.items, {});
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []ArrayListType,
                    _: void,
                ) std.mem.Allocator.Error!void {
                    _ = gpa_opt.?;
                    @memset(values, .empty);
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *ArrayListType,
                    _: void,
                ) DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const len = try Codec(usize).std_int.decode(reader, null, config, {});
                    try value.ensureTotalCapacityPrecise(gpa, len);

                    if (len > value.items.len) {
                        const additional = value.addManyAsSliceAssumeCapacity(len - value.items.len);
                        element_codec.decodeInitMany(gpa, additional, {}) catch |err| {
                            value.shrinkRetainingCapacity(len - additional.len);
                            return err;
                        };
                    } else if (len < value.items.len) {
                        for (value.items[len..]) |*elem| {
                            element_codec.free(gpa, elem, {});
                        }
                        value.shrinkRetainingCapacity(len);
                    }
                    std.debug.assert(value.items.len == len);

                    for (value.items) |*elem| {
                        try element_codec.decodeInto(reader, gpa, config, elem, {});
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const ArrayListType,
                    _: void,
                ) void {
                    const gpa = gpa_opt.?;
                    if (element_codec.freeFn != null) {
                        for (value.items) |*elem| element_codec.free(gpa, elem);
                    }
                    var copy = value.*;
                    copy.deinit(gpa);
                }
            });
        }

        const maybe_array_hm_info: ?ArrayHashMapInfo = .from(V);

        pub fn StdArrayHashMapCtxs(
            key: Codec(if (maybe_array_hm_info) |hm_info| hm_info.K else void),
            val: Codec(if (maybe_array_hm_info) |hm_info| hm_info.V else void),
        ) type {
            return struct {
                pub const EncodeCtx = struct {
                    key: key.EncodeCtx,
                    val: val.EncodeCtx,
                };
                pub const DecodeCtx = struct {
                    key: key.DecodeCtx,
                    val: val.DecodeCtx,
                };
            };
        }

        /// Standard codec for an auto hash map.
        /// Requires allocation, for the hashmap, and possibly for the entries (based on key val codec).
        ///
        /// Decode's initial state is `.empty`. If it is non-empty, it must have been allocated using
        /// the supplied `gpa_opt.?`; it will be resized to the decoded length if necessary, freeing
        /// the discarded elements or initializing added elements using the key/val codec, and decoding
        /// into the existing elements, which must be in a valid initial state conforming to key/val codec's
        /// documented expectations.
        pub fn stdArrayHashMap(
            key_codec: Codec(if (maybe_array_hm_info) |hm_info| hm_info.K else void),
            val_codec: Codec(if (maybe_array_hm_info) |hm_info| hm_info.V else void),
        ) CodecSelf {
            const hm_info = comptime maybe_array_hm_info orelse @compileError(@typeName(V) ++ " is not an array hash map.");
            const Map = std.ArrayHashMapUnmanaged(
                hm_info.K,
                hm_info.V,
                hm_info.Context,
                hm_info.store_hash,
            );
            const Ctxs = StdArrayHashMapCtxs(key_codec, val_codec);
            const EncodeCtx = Ctxs.EncodeCtx;
            const DecodeCtx = Ctxs.DecodeCtx;

            const EncodeCtxParam = switch (hmSpecKind(EncodeCtx)) {
                .some_required => EncodeCtx,
                .all_opt_or_void => ?EncodeCtx,
                .all_void => void,
            };
            const DecodeCtxParam = switch (hmSpecKind(DecodeCtx)) {
                .some_required => DecodeCtx,
                .all_opt_or_void => ?DecodeCtx,
                .all_void => void,
            };

            return .implement(EncodeCtxParam, DecodeCtxParam, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const Map,
                    maybe_ctx: EncodeCtxParam,
                ) EncodeWriterError!void {
                    const key_ctx: key_codec.EncodeCtx = ctx: {
                        const ctx = switch (@typeInfo(key_codec.EncodeCtx)) {
                            .void => break :ctx {},
                            .optional => maybe_ctx orelse break :ctx null,
                            else => maybe_ctx,
                        };
                        break :ctx ctx.key;
                    };
                    const val_ctx: val_codec.EncodeCtx = ctx: {
                        const ctx = switch (@typeInfo(val_codec.EncodeCtx)) {
                            .void => break :ctx {},
                            .optional => maybe_ctx orelse break :ctx null,
                            else => maybe_ctx,
                        };
                        break :ctx ctx.val;
                    };

                    try Codec(usize).std_int.encode(writer, config, &value.count(), {});
                    for (value.keys(), value.values()) |*k, *v| {
                        try key_codec.encode(writer, config, k, key_ctx);
                        try val_codec.encode(writer, config, v, val_ctx);
                    }
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []Map,
                    _: DecodeCtxParam,
                ) std.mem.Allocator.Error!void {
                    _ = gpa_opt.?;
                    @memset(values, .empty);
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *Map,
                    maybe_ctx: DecodeCtxParam,
                ) DecodeReaderError!void {
                    const gpa = gpa_opt.?;
                    const key_ctx, const val_ctx = unwrapDecodeKeyValCtxs(maybe_ctx);

                    const len = try Codec(usize).std_int.decode(reader, null, config, {});
                    try value.ensureTotalCapacity(gpa, len);

                    const original_count = value.count();
                    for (
                        value.keys()[0..@min(len, original_count)],
                        value.values()[0..@min(len, original_count)],
                    ) |*k, *v| {
                        try key_codec.decodeInto(reader, gpa, config, k, key_ctx);
                        try val_codec.decodeInto(reader, gpa, config, v, key_ctx);
                    }

                    value.reIndex(gpa) catch |err| {
                        freeKeysAndVals(gpa, value, maybe_ctx);
                        value.clearRetainingCapacity();
                        return err;
                    };

                    if (len < original_count) {
                        for (
                            value.keys()[len..],
                            value.values()[len..],
                        ) |*k, *v| {
                            key_codec.free(gpa, k, key_ctx);
                            val_codec.free(gpa, v, val_ctx);
                        }
                        value.shrinkRetainingCapacity(len);
                    } else if (len > original_count) for (original_count..len) |_| {
                        const k = try key_codec.decode(reader, gpa, config, key_ctx);
                        errdefer key_codec.free(gpa, &k, key_ctx);

                        const v = try val_codec.decode(reader, gpa, config, val_ctx);
                        errdefer val_codec.free(gpa, &v, val_ctx);

                        if (value.contains(k)) return error.DecodeFailed;
                        value.putAssumeCapacity(k, v);
                    };
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const Map,
                    maybe_ctx: DecodeCtxParam,
                ) void {
                    const gpa = gpa_opt.?;
                    freeKeysAndVals(gpa, value, maybe_ctx);
                    var copy = value.*;
                    copy.deinit(gpa);
                }

                fn freeKeysAndVals(
                    gpa: std.mem.Allocator,
                    value: *const Map,
                    maybe_ctx: DecodeCtxParam,
                ) void {
                    if (key_codec.freeFn == null and val_codec.freeFn == null) return;
                    const key_ctx, const val_ctx = unwrapDecodeKeyValCtxs(maybe_ctx);
                    for (value.keys(), value.values()) |*k, *v| {
                        key_codec.free(gpa, k, key_ctx);
                        val_codec.free(gpa, v, val_ctx);
                    }
                }

                fn unwrapDecodeKeyValCtxs(
                    maybe_ctx: DecodeCtxParam,
                ) struct { key_codec.DecodeCtx, val_codec.DecodeCtx } {
                    const key_ctx: key_codec.DecodeCtx = ctx: {
                        const ctx = switch (@typeInfo(key_codec.DecodeCtx)) {
                            .void => break :ctx {},
                            .optional => maybe_ctx orelse break :ctx null,
                            else => maybe_ctx,
                        };
                        break :ctx ctx.key;
                    };
                    const val_ctx: val_codec.DecodeCtx = ctx: {
                        const ctx = switch (@typeInfo(val_codec.DecodeCtx)) {
                            .void => break :ctx {},
                            .optional => maybe_ctx orelse break :ctx null,
                            else => maybe_ctx,
                        };
                        break :ctx ctx.val;
                    };

                    return .{ key_ctx, val_ctx };
                }
            });
        }

        fn hmSpecKind(comptime EncOrDecCtx: type) enum {
            some_required,
            all_opt_or_void,
            all_void,
        } {
            const void_key_ctx = @FieldType(EncOrDecCtx, "key") == void;
            const void_val_ctx = @FieldType(EncOrDecCtx, "val") == void;

            const opt_key_ctx = @typeInfo(@FieldType(EncOrDecCtx, "key")) == .optional;
            const opt_val_ctx = @typeInfo(@FieldType(EncOrDecCtx, "val")) == .optional;

            const void_or_opt_key_ctx = void_key_ctx or opt_key_ctx;
            const void_or_opt_val_ctx = void_val_ctx or opt_val_ctx;

            if (void_key_ctx and void_val_ctx) return .all_void;
            if (void_or_opt_key_ctx and void_or_opt_val_ctx) return .all_opt_or_void;
            return .some_required;
        }

        /// The `Child` of `V`. Corresponds to `Child` in all of the following,
        /// and all permutations of their cv-qualified forms: `?C`, `*C`.
        /// NOTE: if `Element != noreturn`, this may be one of: `[n]Element`, `@Vector(n, Element)`.
        pub const Child = switch (@typeInfo(V)) {
            .optional => |optional_info| optional_info.child,
            .pointer => |ptr_info| switch (ptr_info.size) {
                .one => ptr_info.child,
                else => noreturn,
            },
            else => noreturn,
        };

        /// The `Element` of `V`. Corresponds to `E` in all of the following, and all permutations of their cv-qualified forms:
        /// - []E
        /// - [*]E
        /// - `[n]E`
        /// - `*[n]E`
        /// - `@Vector(n, E)`
        /// - `*@Vector(n, E)`
        pub const Element = switch (@typeInfo(V)) {
            .array => |array_info| array_info.child,
            .vector => |vec_info| vec_info.child,
            .pointer => |ptr_info| switch (ptr_info.size) {
                .one => switch (@typeInfo(ptr_info.child)) {
                    .array => |array_info| array_info.child,
                    .vector => |vec_info| vec_info.child,
                    else => noreturn,
                },
                .slice => ptr_info.child,
                .many => ptr_info.child,
                else => noreturn,
            },
            else => noreturn,
        };

        /// A struct with the same set of field names as `V` (a struct or a union), wherein each field
        /// has a type `Codec(@FieldType(V, field_name))`, where `field_name` is the corresponding name
        /// of the field.
        /// If `V` is a tuple, this is also a tuple.
        pub const Fields = switch (@typeInfo(V)) {
            inline //
            .@"struct",
            .@"union",
            => |info, tag| @Type(.{ .@"struct" = .{
                .layout = .auto,
                .backing_integer = null,
                .is_tuple = tag == .@"struct" and info.is_tuple,
                .decls = &.{},
                .fields = fields: {
                    var fields: [info.fields.len]std.builtin.Type.StructField = undefined;
                    for (&fields, info.fields) |*ctx_field, v_field| {
                        const FieldCodec = Codec(v_field.type);
                        ctx_field.* = .{
                            .name = v_field.name,
                            .type = *const FieldCodec,
                            .default_value_ptr = null,
                            .is_comptime = false,
                            .alignment = @alignOf(FieldCodec),
                        };
                    }
                    break :fields &fields;
                },
            } }),
            else => noreturn,
        };

        pub fn FieldContexts(field_codecs: Fields) struct { type, type } {
            const fields, const is_tuple = switch (@typeInfo(V)) {
                .@"struct" => |s_info| .{ s_info.fields, s_info.is_tuple },
                .@"union" => |u_info| .{ u_info.fields, false },
                else => @compileError("doesn't apply for " ++ @typeName(V)),
            };

            const FieldKindState = enum {
                some_required,
                all_opt_or_void,
                all_void,
            };

            var field_kind_state_enc: FieldKindState = .all_void;
            var encode_fields: [fields.len]std.builtin.Type.StructField = undefined;

            var field_kind_state_dec: FieldKindState = .all_void;
            var decode_fields: [fields.len]std.builtin.Type.StructField = undefined;

            @setEvalBranchQuota(fields.len + 2);
            for (&encode_fields, &decode_fields, fields) |*encode_field, *decode_field, field| {
                const codec_field: *const Codec(field.type) = @field(field_codecs, field.name);

                const void_enc = codec_field.EncodeCtx == void;
                const opt_enc = @typeInfo(codec_field.EncodeCtx) == .optional;
                if (field_kind_state_enc != .some_required and !void_enc) {
                    field_kind_state_enc = if (opt_enc) .all_opt_or_void else .some_required;
                }

                encode_field.* = .{
                    .name = field.name,
                    .type = codec_field.EncodeCtx,
                    .default_value_ptr = if (void_enc) @ptrCast(&{}) else null,
                    .is_comptime = false,
                    .alignment = @alignOf(codec_field.EncodeCtx),
                };

                const void_dec = codec_field.DecodeCtx == void;
                const opt_dec = @typeInfo(codec_field.DecodeCtx) == .optional;
                if (field_kind_state_dec != .some_required and !void_dec) {
                    field_kind_state_dec = if (opt_dec) .all_opt_or_void else .some_required;
                }
                decode_field.* = .{
                    .name = field.name,
                    .type = codec_field.DecodeCtx,
                    .default_value_ptr = if (void_dec) @ptrCast(&{}) else null,
                    .is_comptime = false,
                    .alignment = @alignOf(codec_field.DecodeCtx),
                };
            }

            const Enc = @Type(.{ .@"struct" = .{
                .layout = .auto,
                .backing_integer = null,
                .is_tuple = is_tuple,
                .decls = &.{},
                .fields = &encode_fields,
            } });
            const Dec = @Type(.{ .@"struct" = .{
                .layout = .auto,
                .backing_integer = null,
                .is_tuple = is_tuple,
                .decls = &.{},
                .fields = &decode_fields,
            } });

            return .{
                switch (field_kind_state_enc) {
                    .all_void => void,
                    .all_opt_or_void => ?Enc,
                    .some_required => Enc,
                },
                switch (field_kind_state_dec) {
                    .all_void => void,
                    .all_opt_or_void => ?Dec,
                    .some_required => Dec,
                },
            };
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

const ArrayHashMapInfo = struct {
    K: type,
    V: type,
    Context: type,
    store_hash: bool,

    pub fn from(comptime T: type) ?ArrayHashMapInfo {
        if (@typeInfo(T) != .@"struct") return null;

        if (!@hasDecl(T, "KV")) return null;
        if (@TypeOf(&T.KV) != *const type) return null;
        const KV = T.KV;

        if (@typeInfo(KV) != .@"struct") return null;
        if (!@hasField(KV, "key")) return null;
        if (!@hasField(KV, "value")) return null;
        const K = @FieldType(KV, "key");
        const V = @FieldType(KV, "value");

        if (!@hasDecl(T, "Hash")) return null;
        if (@TypeOf(&T.Hash) != *const type) return null;
        const store_hash = switch (T.Hash) {
            u32 => true,
            void => false,
            else => return null,
        };

        if (!@hasDecl(T, "popContext")) return null;
        const pop_ctx_fn_info = switch (@typeInfo(@TypeOf(T.popContext))) {
            .@"fn" => |fn_info| fn_info,
            else => return null,
        };
        if (pop_ctx_fn_info.params.len != 2) return null;
        const Context = pop_ctx_fn_info.params[1].type orelse return null;

        if (T != std.ArrayHashMapUnmanaged(K, V, Context, store_hash)) return null;

        return .{
            .K = K,
            .V = V,
            .Context = Context,
            .store_hash = store_hash,
        };
    }
};

const testing = @import("testing.zig");

inline fn encIntLit(comptime config: Config, comptime int: anytype) []const u8 {
    const Int = if (@TypeOf(int) == usize) u64 else @TypeOf(int);
    comptime return switch (config.int) {
        .fixint => std.mem.toBytes(std.mem.nativeTo(Int, int, config.endian)),
        .varint => varint.encodedLiteral(config.endian, int),
    };
}

inline fn encStrLit(comptime config: Config, comptime str: []const u8) []const u8 {
    return encIntLit(config, @as(usize, str.len)) ++ str;
}

test "std_void" {
    var null_reader: std.Io.Reader = .failing;
    var null_writer: std.Io.Writer.Discarding = .init(&.{});
    const void_codec: Codec(void) = .std_void;
    try std.testing.expectEqual({}, void_codec.encode(&null_writer.writer, .default, &{}, {}));
    try std.testing.expectEqual({}, void_codec.decode(&null_reader, null, .default, {}));
    try std.testing.expectEqual(0, void_codec.encodedSize(.default, &{}, {}));
}

test "std_byte" {
    const byte_codec: Codec(u8) = .std_byte;
    try std.testing.expectEqual('f', byte_codec.decodeSliceExact(&.{'f'}, null, .default, {}));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, null, .default, {}));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, null, .default, {}));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeSliceExact(&.{}, null, .default, {}));
    try std.testing.expectError(error.Overlong, byte_codec.decodeSliceExact("bar", null, .default, {}));
    try std.testing.expectEqual(1, byte_codec.encodedSize(.default, &'z', {}));
}

test "std_bool" {
    const bool_codec: Codec(bool) = .std_bool;
    try std.testing.expectEqual(false, bool_codec.decodeSliceExact(&.{0}, null, .default, null));
    try std.testing.expectEqual(true, bool_codec.decodeSliceExact(&.{1}, null, .default, null));

    var diag: Codec(bool).StdBoolDecodeDiag = .init;
    try std.testing.expectError(error.DecodeFailed, bool_codec.decodeSliceExact(&.{2}, null, .default, &diag));
    try std.testing.expectEqual(2, diag.real_byte);

    try std.testing.expectError(error.EndOfStream, bool_codec.decodeSliceExact(&.{}, null, .default, &diag));
    try std.testing.expectError(error.Overlong, bool_codec.decodeSliceExact(&.{ 1, 0 }, null, .default, &diag));
    try std.testing.expectEqual(1, bool_codec.encodedSize(.default, &false, {}));
    try std.testing.expectEqual(1, bool_codec.encodedSize(.default, &true, {}));
}

test "std_int" {
    const u32_codec: Codec(u32) = .std_int;
    const config: Config = .{ .endian = .little, .int = .varint };

    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, {}, {}, 250, &.{250});
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, {}, {}, 251, &.{ 251, 251, 0 });
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, {}, {}, 300, &.{ 251, 0x2C, 1 });
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, {}, {}, std.math.maxInt(u16), &.{ 251, 0xFF, 0xFF });
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, {}, {}, std.math.maxInt(u16) + 1, &.{ 252, 0, 0, 1, 0 });

    try testCodecRoundTrips(i16, .std_int, {}, {}, &intTestEdgeCases(i16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(u16, .std_int, {}, {}, &intTestEdgeCases(u16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(i32, .std_int, {}, {}, &intTestEdgeCases(i32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u32, .std_int, {}, {}, &intTestEdgeCases(u32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i64, .std_int, {}, {}, &intTestEdgeCases(i64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u64, .std_int, {}, {}, &intTestEdgeCases(u64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i128, .std_int, {}, {}, &intTestEdgeCases(i128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u128, .std_int, {}, {}, &intTestEdgeCases(u128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i256, .std_int, {}, {}, &intTestEdgeCases(i256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u256, .std_int, {}, {}, &intTestEdgeCases(u256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(isize, .std_int, {}, {}, &intTestEdgeCases(isize) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(usize, .std_int, {}, {}, &intTestEdgeCases(usize) ++ .{ 1, 5, 1000000000, 32, 8 });
}

test "std_float" {
    try testCodecRoundTrips(f32, .std_float, {}, {}, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f32, .std_float, {}, {}, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f64, .std_float, {}, {}, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f64, .std_float, {}, {}, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f32, .std_float, {}, {}, &floatTestEdgeCases(f32));
    try testCodecRoundTrips(f64, .std_float, {}, {}, &floatTestEdgeCases(f64));
}

test "std_utf8_codepoint" {
    try std.testing.expectEqual(1, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{7F}', {}));
    try std.testing.expectEqual(2, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{ff}', {}));
    try std.testing.expectEqual(3, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{fff}', {}));
    try std.testing.expectEqual(4, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{fffff}', {}));
    try testCodecRoundTrips(u8, .std_utf8_codepoint, {}, {}, &@as([128]u8, std.simd.iota(u8, 128))); // ascii
    inline for (.{ u1, u2, u3, u4, u5, u6, u7, u8, u16, u21, u32 }) |AsciiInt| {
        const max_val = @min(127, std.math.maxInt(AsciiInt));
        const ascii_vals: [max_val + 1]AsciiInt = std.simd.iota(AsciiInt, max_val + 1);
        try testCodecRoundTrips(
            AsciiInt,
            .std_utf8_codepoint,
            {},
            {},
            &ascii_vals,
        );
    }
    try testCodecRoundTrips(u21, .std_utf8_codepoint, {}, {}, &.{ 'à', 'á', 'é', 'è', 'ì', 'í', 'ò', 'ó', 'ù', 'ú' });
    try testCodecRoundTrips(u21, .std_utf8_codepoint, {}, {}, &.{ '\u{2100}', '\u{3100}', '\u{FFAAA}', '\u{FFFFF}', '\u{FFFFF}' });
}

test "stdOptional" {
    try testCodecRoundTrips(?void, .stdOptional(.std_void), {}, .{ .diag = null, .pl = {} }, &.{ null, {}, null, {}, null, {} });
    try testCodecRoundTrips(?bool, .stdOptional(.std_bool), {}, .{ .diag = null, .pl = null }, &.{
        null, false, null, true, null, true,
        null, false, true, true, null, false,
    });
    try testCodecRoundTrips(?u32, .stdOptional(.std_int), {}, .{ .diag = null, .pl = {} }, &.{ null, 4, null, 10000, null, 100000000 });
    try testCodecRoundTrips(?i64, .stdOptional(.std_int), {}, .{ .diag = null, .pl = {} }, &.{ null, -7, null, 20000, null, -100000000 });

    const codec: Codec(?u32) = .stdOptional(.std_int);
    const config: Config = .{ .endian = .little, .int = .varint };
    try testEncodedBytesAndRoundTrip(?u32, codec, config, {}, .{ .diag = null, .pl = {} }, 3, "\x01" ++ "\x03");
    try testEncodedBytesAndRoundTrip(?u32, codec, config, {}, .{ .diag = null, .pl = {} }, null, "\x00");
    try testEncodedBytesAndRoundTrip(?u32, codec, config, {}, .{ .diag = null, .pl = {} }, 251, "\x01" ++ "\xFB\xFB\x00");
}

test "stdStruct" {
    const S = struct {
        a: u32,
        b: f64,

        const bk_codec: Codec(@This()) = .stdStruct(.{
            .a = &.std_int,
            .b = &.std_float,
        });
    };

    const struct_test_edge_cases = comptime blk: {
        const ints = intTestEdgeCases(u32);
        const floats = floatTestEdgeCases(f64);
        var struct_test_edge_cases: [ints.len * floats.len]S = undefined;

        for (ints, 0..) |int, i| for (floats, 0..) |float, j| {
            struct_test_edge_cases[i + j * ints.len] = .{ .a = int, .b = float };
        };

        break :blk struct_test_edge_cases;
    };
    try testCodecRoundTrips(S, S.bk_codec, {}, {}, &struct_test_edge_cases);

    try testEncodedBytesAndRoundTrip(
        S,
        S.bk_codec,
        .{ .endian = .little, .int = .varint },
        {},
        {},
        .{ .a = 1, .b = 0 },
        "\x01" ++ std.mem.toBytes(@as(f64, 0)),
    );
}

test "stdUnion" {
    const U = union(enum) {
        void,
        char: u8,
        int: u32,
        float: f64,
        record: struct {
            a: u64,
            b: u16,
            c: enum { foo, bar },
        },

        const bk_codec: Codec(@This()) = .stdUnion(null, .{
            .void = &.std_void,
            .char = &.std_byte,
            .int = &.std_int,
            .float = &.std_float,
            .record = &.stdStruct(.{
                .a = &.std_int,
                .b = &.std_int,
                .c = &.std_discriminant,
            }),
        });
    };

    try testCodecRoundTrips(
        U,
        U.bk_codec,
        {},
        .{
            .diag = null,
            .pl = null,
        },
        &.{
            .void,
            .{ .char = 42 },
            .{ .int = 1111111111 },
            .{ .float = -7 },
            .{ .record = .{ .a = 1, .b = 2, .c = .foo } },
        },
    );
}

test "std_byte_array" {
    try testCodecRoundTrips([3]u8, .std_byte_array, {}, {}, &.{ "foo".*, "bar".*, "baz".* });
}

test "stdArray" {
    try testCodecRoundTrips([2]u64, .stdArray(.std_int), {}, {}, @ptrCast(&intTestEdgeCases(u64) ++ intTestEdgeCases(u64)));
    try testCodecRoundTrips([2]u64, .stdArray(.std_int), {}, {}, &.{
        .{ 1, 2 },
        .{ 61, 313131 },
        @splat(111111111),
    });

    try testCodecRoundTrips([2]f32, .stdArray(.std_float), {}, {}, @ptrCast(&floatTestEdgeCases(f32) ++ floatTestEdgeCases(f32)));
    try testCodecRoundTrips([2]f64, .stdArray(.std_float), {}, {}, @ptrCast(&floatTestEdgeCases(f64) ++ floatTestEdgeCases(f64)));
    try testCodecRoundTrips(@Vector(2, f32), .stdArray(.std_float), {}, {}, &.{
        .{ -1.0, 2 },
        .{ 61, -313131 },
        @splat(111111111.0),
    });
}

test "std_byte_slice" {
    try testCodecRoundTrips([]const u8, .std_byte_slice, {}, {}, &.{
        &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 }, "foo",  "bar",  "baz",
        &.{ 127, std.math.maxInt(u8) },  "fizz", "buzz", "fizzbuzz",
    });
}

test "stdSlice" {
    try testCodecRoundTrips([]const u32, .stdSlice(.std_int), {}, {}, &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5, 6 },
        &.{ 7, 8, 9, 10, 11 },
        &.{ 12, 13, 14, 15, 16, 17 },
        &.{ 18, 19, 20, 21, 22, 23, 24 },
        &.{ 25, 26, 27, 28, 29, 30, 31, 32 },
    });
}

test "std_byte_array_ptr" {
    try testCodecRoundTrips(*const [3]u8, .std_byte_array_ptr, {}, {}, &.{
        "foo",
        "bar",
        "baz",
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5 },
        &.{ 7, 8, 9 },
        &.{ 12, 13, 14 },
        &.{ 18, 19, 20 },
        &.{ 25, 26, 27 },
    });
}

test "stdArrayPtr" {
    try testCodecRoundTrips(*const [3]u32, .stdArrayPtr(.std_int), {}, {}, &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5 },
        &.{ 7, 8, 9 },
        &.{ 12, 13, 14 },
        &.{ 18, 19, 20 },
        &.{ 25, 26, 27 },
    });
}

test "stdSingleItemPtr" {
    try testCodecRoundTrips(*const u32, .stdSingleItemPtr(.std_int), {}, {}, &.{
        &0, &1, &2, &10000, &std.math.maxInt(u32),
    });
}

test "stdArrayList" {
    const gpa = std.testing.allocator;

    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try testCodecRoundTrips(std.ArrayListUnmanaged(u32), .stdArrayList(.std_int), {}, {}, &.{
        .empty,
        .fromOwnedSlice(try arena.dupe(u32, &.{ 1, 2, 3 })),
        .fromOwnedSlice(try arena.dupe(u32, &intTestEdgeCases(u32))),
    });
    try testEncodedBytesAndRoundTrip(
        std.ArrayListUnmanaged(u16),
        .stdArrayList(.std_int),
        .{ .endian = .little, .int = .varint },
        {},
        {},
        .fromOwnedSlice(try arena.dupe(u16, &.{ 0, 1, 250, 251 })),
        &[_]u8{4} ++ .{0} ++ .{1} ++ .{250} ++ .{ 251, 251, 0 },
    );

    var list: std.ArrayListUnmanaged([]const u8) = .empty;
    defer list.deinit(gpa);
    defer for (list.items) |str| gpa.free(str);
    try list.ensureTotalCapacityPrecise(gpa, 4);
    const original = try gpa.dupe(u8, "foo");
    list.appendAssumeCapacity(original);
    list.appendAssumeCapacity(try gpa.dupe(u8, "bar"));
    list.appendAssumeCapacity(try gpa.dupe(u8, "baz"));
    list.appendAssumeCapacity(try gpa.dupe(u8, "boo"));

    const str_array_list_codec: Codec(std.ArrayListUnmanaged([]const u8)) = .stdArrayList(.std_byte_slice);
    _ = try str_array_list_codec.decodeSliceInto(
        .{2} ++ .{4} ++ "fizz" ++ .{4} ++ "buzz",
        gpa,
        .{ .endian = .little, .int = .varint },
        &list,
        {},
    );
    try std.testing.expectEqualDeep(&[_][]const u8{ "fizz", "buzz" }, list.items);
}

test "stdArrayHashMap" {
    const gpa = std.testing.allocator;

    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const compare_ctx = struct {
        pub fn compare(expected: anytype, actual: anytype) !bool {
            const T = @TypeOf(expected, actual);
            if (ArrayHashMapInfo.from(T) != null) {
                try testing.expectEqualDeepWithOverrides(expected.keys(), actual.keys(), @This());
                try testing.expectEqualDeepWithOverrides(expected.values(), actual.values(), @This());
                return true;
            }
            return false;
        }
    };

    const MapU32U32 = std.AutoArrayHashMapUnmanaged(u32, u32);
    try testCodecRoundTripsInner(
        MapU32U32,
        .stdArrayHashMap(.std_int, .std_int),
        {},
        {},
        &.{
            .empty,
            try initArrayHashMap(arena, MapU32U32, &.{ .{ 1, 2 }, .{ 3, 4 } }),
            try initArrayHashMap(arena, MapU32U32, &.{ .{ 5, 6 }, .{ 7, 8 }, .{ 9, 10 } }),
        },
        compare_ctx,
    );

    const MapStrU16 = std.StringArrayHashMapUnmanaged(u16);
    const lev: Config = comptime .cfg(.little, .varint);
    try testEncodedBytesAndRoundTripInner(
        MapStrU16,
        .stdArrayHashMap(.std_byte_slice, .std_int),
        lev,
        {},
        {},
        try initArrayHashMap(arena, MapStrU16, &.{ .{ "foo", 2 }, .{ "bar", 4 } }),
        encIntLit(lev, 2) ++
            (encStrLit(lev, "foo") ++ encIntLit(lev, 2)) ++
            (encStrLit(lev, "bar") ++ encIntLit(lev, 4)),
        compare_ctx,
    );

    var list: MapStrU16 = .empty;
    defer list.deinit(gpa);
    defer for (list.keys()) |str| gpa.free(str);
    try list.ensureTotalCapacity(gpa, 4);

    list.putAssumeCapacity(try gpa.dupe(u8, "foo"), 100);
    list.putAssumeCapacity(try gpa.dupe(u8, "bar"), 150);
    list.putAssumeCapacity(try gpa.dupe(u8, "baz"), 200);
    list.putAssumeCapacity(try gpa.dupe(u8, "fizz"), 250);
    list.putAssumeCapacity(try gpa.dupe(u8, "buzz"), 300);

    const map_str_u16_codec: Codec(MapStrU16) =
        .stdArrayHashMap(.std_byte_slice, .std_int);
    _ = try map_str_u16_codec.decodeSliceInto(
        encIntLit(lev, 2) ++
            (encStrLit(lev, "big") ++ encIntLit(lev, 350)) ++
            (encStrLit(lev, "small") ++ encIntLit(lev, 400)),
        gpa,
        lev,
        &list,
        {},
    );
    try std.testing.expectEqualDeep(&[_][]const u8{ "big", "small" }, list.keys());
    try std.testing.expectEqualSlices(u16, &.{ 350, 400 }, list.values());

    _ = try map_str_u16_codec.decodeSliceInto(
        encIntLit(lev, 4) ++
            (encStrLit(lev, "a") ++ encIntLit(lev, 450)) ++
            (encStrLit(lev, "bc") ++ encIntLit(lev, 500)) ++
            (encStrLit(lev, "def") ++ encIntLit(lev, 550)) ++
            (encStrLit(lev, "ghij") ++ encIntLit(lev, 600)),
        gpa,
        lev,
        &list,
        {},
    );
    try std.testing.expectEqualDeep(&[_][]const u8{ "a", "bc", "def", "ghij" }, list.keys());
    try std.testing.expectEqualSlices(u16, &.{ 450, 500, 550, 600 }, list.values());
}

fn initArrayHashMap(
    gpa: std.mem.Allocator,
    comptime Hm: type,
    key_vals: []const blk: {
        const hm_info = ArrayHashMapInfo.from(Hm) orelse
            @compileError(@typeName(Hm) ++ "is not a hash map");
        break :blk struct { hm_info.K, hm_info.V };
    },
) !Hm {
    var hm: Hm = .empty;
    errdefer hm.deinit(gpa);
    try hm.ensureTotalCapacity(gpa, @intCast(key_vals.len));
    for (key_vals) |kv| {
        const k, const v = kv;
        hm.putAssumeCapacity(k, v);
    }
    return hm;
}

test "decodeSliceIgnoreLength" {
    const config: Config = .{ .endian = .little, .int = .varint };
    const overlong_varint_src = [_]u8{ 250, 1 };
    try std.testing.expectEqual(
        250,
        Codec(u32).std_int.decodeSliceExact((&overlong_varint_src)[0..1], null, config, {}),
    );
    try std.testing.expectError(
        error.Overlong,
        Codec(u32).std_int.decodeSliceExact(&overlong_varint_src, null, config, {}),
    );
    try std.testing.expectEqual(
        250,
        Codec(u32).std_int.decodeSliceIgnoreLength(&overlong_varint_src, null, config, {}),
    );
}

test "optional slice memory re-use" {
    const gpa = std.testing.allocator;

    const codec: Codec(?[]const u8) = .stdOptional(.std_byte_slice);

    const expected: ?[]const u8 = "foo";
    const expected_encoded_bytes = try codec.encodeAlloc(gpa, .default, &expected, {});
    defer gpa.free(expected_encoded_bytes);

    var actual: ?[]const u8 = try gpa.alloc(u8, 100);
    defer if (actual) |res| gpa.free(res);
    try std.testing.expectEqual(
        expected_encoded_bytes.len,
        codec.decodeSliceInto(expected_encoded_bytes, gpa, .default, &actual, .{ .diag = null, .pl = {} }),
    );
    try std.testing.expectEqualDeep(expected, actual);
}

test "union memory re-use" {
    const gpa = std.testing.allocator;
    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const U = union(enum) {
        a: std.ArrayListUnmanaged(u8),
        b: []const u8,

        const bk_codec: Codec(@This()) = .stdUnion(.a, .{
            .a = &.stdArrayList(.std_byte),
            .b = &.std_byte_slice,
        });
    };

    var u: U = .{ .a = .empty };
    defer switch (u) {
        .a => |*a| a.deinit(gpa),
        .b => |b| gpa.free(b),
    };

    try std.testing.expectEqual(4, U.bk_codec.decodeSliceInto(
        &[_]u8{0} ++ .{2} ++ .{ 45, 56 },
        gpa,
        .default,
        &u,
        .{ .diag = null, .pl = {} },
    ));
    try std.testing.expectEqualDeep(
        U{ .a = .fromOwnedSlice(try arena.dupe(u8, &.{ 45, 56 })) },
        u,
    );

    // default implementation doesn't re-use the memory in between different variants.
    try std.testing.expectEqual(5, U.bk_codec.decodeSliceInto(
        &[_]u8{1} ++ .{3} ++ .{ 99, 66, 33 },
        gpa,
        .default,
        &u,
        .{ .diag = null, .pl = {} },
    ));
    try std.testing.expectEqualDeep(
        U{ .b = &.{ 99, 66, 33 } },
        u,
    );
}

fn floatTestEdgeCases(comptime F: type) [18]F {
    const inf = std.math.inf(F);
    const max = std.math.floatMax(F);
    const eps = std.math.floatEps(F);
    const min = std.math.floatMin(F);
    const min_true = std.math.floatTrueMin(F);
    return .{
        0.0,      -0.0,
        min_true, -min_true,
        min,      -min,
        0.1,      -0.1,
        0.2,      -0.2,
        0.3,      -0.3,
        eps,      -eps,
        max,      -max,
        inf,      -inf,
    };
}

fn intTestEdgeCases(comptime T: type) [23]T {
    const min_int = std.math.minInt(T);
    const max_int = std.math.maxInt(T);
    return .{
        // edge cases
        min_int,

        @max(-1, min_int),

        0,

        @min(1, max_int),

        @min(251 - 1, max_int),
        @min(251 + 0, max_int),
        @min(251 + 1, max_int),

        @min((1 << 16) - 1, max_int),
        @min((1 << 16) + 0, max_int),
        @min((1 << 16) + 1, max_int),

        @min((1 << 32) - 1, max_int),
        @min((1 << 32) + 0, max_int),
        @min((1 << 32) + 1, max_int),

        @min((1 << 64) - 1, max_int),
        @min((1 << 64) + 0, max_int),
        @min((1 << 64) + 1, max_int),

        @min((1 << 128) - 1, max_int),
        @min((1 << 128) + 0, max_int),
        @min((1 << 128) + 1, max_int),

        @min((1 << 256) - 1, max_int),
        @min((1 << 256) + 0, max_int),
        @min((1 << 256) + 1, max_int),

        max_int,
    };
}

/// Test that `value` encodes into the same bytes as `expected`, and then
/// also test whether `expected` decodes back into the same as `value`.
fn testEncodedBytesAndRoundTrip(
    comptime T: type,
    codec: Codec(T),
    config: Config,
    enc_ctx: codec.EncodeCtx,
    dec_ctx: codec.DecodeCtx,
    value: T,
    expected: []const u8,
) !void {
    try testEncodedBytesAndRoundTripInner(
        T,
        codec,
        config,
        enc_ctx,
        dec_ctx,
        value,
        expected,
        struct {
            pub fn compare(_: anytype, _: anytype) !bool {
                return false;
            }
        },
    );
}

fn testEncodedBytesAndRoundTripInner(
    comptime T: type,
    codec: Codec(T),
    config: Config,
    enc_ctx: codec.EncodeCtx,
    dec_ctx: codec.DecodeCtx,
    original: T,
    expected_bytes: []const u8,
    /// Expects methods:
    /// * `fn compare(expected: anytype, actual: @TypeOf(expected)) !bool`:
    ///   Should return true if the values were compared, and otherwise false
    ///   to fall back to default handling of comparison.
    compare_ctx: anytype,
) !void {
    const actual_bytes = try codec.encodeAlloc(std.testing.allocator, config, &original, enc_ctx);
    defer std.testing.allocator.free(actual_bytes);
    try std.testing.expectEqualSlices(u8, expected_bytes, actual_bytes);

    const actual_value = codec.decodeSliceExact(actual_bytes, std.testing.allocator, config, dec_ctx);
    defer if (actual_value) |*unwrapped| codec.free(std.testing.allocator, unwrapped, dec_ctx) else |_| {};
    try testing.expectEqualDeepWithOverrides(original, actual_value, compare_ctx);
}

fn testCodecRoundTrips(
    comptime T: type,
    codec: Codec(T),
    enc_ctx: codec.EncodeCtx,
    dec_ctx: codec.DecodeCtx,
    values: []const T,
) !void {
    try testCodecRoundTripsInner(
        T,
        codec,
        enc_ctx,
        dec_ctx,
        values,
        struct {
            pub fn compare(_: anytype, _: anytype) !bool {
                return false;
            }
        },
    );
}

fn testCodecRoundTripsInner(
    comptime T: type,
    codec: Codec(T),
    enc_ctx: codec.EncodeCtx,
    dec_ctx: codec.DecodeCtx,
    values: []const T,
    /// Expects methods:
    /// * `fn compare(expected: anytype, actual: @TypeOf(expected)) !bool`:
    ///   Should return true if the values were compared, and otherwise false
    ///   to fall back to default handling of comparison.
    compare_ctx: anytype,
) !void {
    var buffer: std.ArrayListUnmanaged(u8) = .empty;
    defer buffer.deinit(std.testing.allocator);

    const cfg_permutations = [_]Config{
        .{ .int = .varint, .endian = .little },
        .{ .int = .varint, .endian = .big },
        .{ .int = .fixint, .endian = .little },
        .{ .int = .fixint, .endian = .big },
    };
    for (cfg_permutations) |config| {
        {
            buffer.clearRetainingCapacity();
            var encoded_writer_state: std.Io.Writer.Allocating = .fromArrayList(std.testing.allocator, &buffer);
            defer buffer = encoded_writer_state.toArrayList();
            const encoded_writer: *std.Io.Writer = &encoded_writer_state.writer;
            for (values) |int| try codec.encode(encoded_writer, config, &int, enc_ctx);
        }

        var encoded_reader: std.Io.Reader = .fixed(buffer.items);
        for (values, 0..) |expected, i| {
            const actual = codec.decode(
                &encoded_reader,
                std.testing.allocator,
                config,
                dec_ctx,
            );
            defer if (actual) |*unwrapped| {
                codec.free(std.testing.allocator, unwrapped, dec_ctx);
            } else |_| {};
            errdefer std.log.err("[{d}]: expected '{any}', actual: '{any}'", .{ i, expected, actual });
            try testing.expectEqualDeepWithOverrides(expected, actual, compare_ctx);
        }
        try std.testing.expectEqual(0, encoded_reader.bufferedLen());
    }
}

const std = @import("std");

pub const IntEncoding = enum {
    varint,
    fixint,
};

pub const EncodeError = std.Io.Writer.Error || error{EncodeFailed};
pub const DecodeError = std.Io.Reader.Error || error{DecodeFailed};

/// This represents an encoding & decoding scheme for a value of type `V`,
/// with behaviour defined by callbacks and an optional type-erased context.
///
/// NOTE: many methods in and adjacent to `Codec` are `inline` in order to propagate comptime-knowness.
pub fn Codec(comptime V: type) type {
    return struct {
        /// This is to be used by the codec implementation to modify behaviour, and/or report additional context.
        ctx: CtxPtr,
        /// Serializes `value.*` to the `writer` stream.
        encodeFn: *const fn (ctx: CtxPtr, writer: *std.Io.Writer, value: *const V) EncodeError!void,
        /// Deserializes into `value.*` from the `reader` stream.
        decodeFn: *const fn (ctx: CtxPtr, reader: *std.Io.Reader, value: *V) DecodeError!void,
        const CodecSelf = @This();

        pub inline fn encode(
            self: CodecSelf,
            writer: *std.Io.Writer,
            value: *const V,
        ) EncodeError!void {
            return self.encodeFn(self.ctx, writer, value);
        }

        pub inline fn decodeCopy(
            self: CodecSelf,
            reader: *std.Io.Reader,
        ) DecodeError!V {
            var value: V = undefined;
            try self.decodeInto(reader, &value);
            return value;
        }

        pub inline fn decodeInto(
            self: CodecSelf,
            reader: *std.Io.Reader,
            value: *V,
        ) DecodeError!void {
            return self.decodeFn(self.ctx, reader, value);
        }

        // -- Standard Codecs -- //

        /// Standard codec for a byte.
        /// Never fails to encode or decode.
        pub const byte: Codec(u8) = .implement(struct {
            pub fn encode(writer: *std.Io.Writer, value: *const u8) EncodeError!void {
                try writer.writeByte(value.*);
            }
            pub fn decode(reader: *std.Io.Reader, value: *u8) DecodeError!void {
                value.* = try reader.takeByte();
            }
        });

        /// Standard codec for a boolean.
        /// Failure to decode indicates a byte value other than 0 or 1.
        pub const boolean: Codec(bool) = .implement(struct {
            pub fn encode(writer: *std.Io.Writer, value: *const bool) EncodeError!void {
                try writer.writeByte(@intFromBool(value.*));
            }
            pub fn decode(reader: *std.Io.Reader, value: *bool) DecodeError!void {
                value.* = switch (try reader.takeByte()) {
                    0 => false,
                    1 => true,
                    else => return error.DecodeFailed,
                };
            }
        });

        // -- Helpers for safely implementing codecs -- //

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, value: *const V) EncodeError!void { ... }
        /// fn decode(reader: *std.Io.Reader, value: *V) DecodeError!void { ... }
        /// ```
        /// Returns a stateless codec with the wrapped type-erased encode/decode method callbacks.
        pub inline fn implement(comptime methods: type) CodecSelf {
            const erased = struct {
                fn encodeFn(ctx: CtxPtr, writer: *std.Io.Writer, value: *const V) EncodeError!void {
                    _ = &ctx.null;
                    try methods.encode(writer, value);
                }
                fn decodeFn(ctx: CtxPtr, reader: *std.Io.Reader, value: *V) DecodeError!void {
                    _ = &ctx.null;
                    try methods.decode(reader, value);
                }
            };

            return .{
                .ctx = .none,
                .encodeFn = erased.encodeFn,
                .decodeFn = erased.decodeFn,
            };
        }

        /// Expects `ctx_ptr` to be a pointer to a value of a type with the following methods associated:
        /// ```zig
        /// fn encode(ctx_ptr: @TypeOf(ctx_ptr), writer: *std.Io.Writer, value: *const V) EncodeError!void { ... }
        /// fn decode(ctx_ptr: @TypeOf(ctx_ptr), reader: *std.Io.Reader, value: *V) DecodeError!void { ... }
        /// ```
        /// Returns a codec containing the type-erased `ctx_ptr` with wrapped type-erased encode/decode method callbacks.
        pub inline fn implementPtr(ctx_ptr: anytype) CodecSelf {
            const CtxImpl = @TypeOf(ctx_ptr.*);

            const erased = struct {
                fn encodeFn(ctx: CtxPtr, writer: *std.Io.Writer, value: *const V) EncodeError!void {
                    try ctx.toPtr(CtxImpl).encode(writer, value);
                }
                fn decodeFn(ctx: CtxPtr, reader: *std.Io.Reader, value: *V) DecodeError!void {
                    try ctx.toPtr(CtxImpl).decode(reader, value);
                }
            };

            return .{
                .ctx = .fromPtr(ctx_ptr),
                .encodeFn = erased.encodeFn,
                .decodeFn = erased.decodeFn,
            };
        }
    };
}

pub const CtxPtr = union {
    null: void,
    mut: *anyopaque,
    immut: *const anyopaque,

    pub const none: CtxPtr = .{ .null = {} };

    pub inline fn fromPtr(any_ptr: anytype) CtxPtr {
        const P = @TypeOf(any_ptr);
        const ptr_info = switch (@typeInfo(P)) {
            .pointer => |ptr_info| ptr_info,
            else => @compileError("Expected pointer, got " ++ @typeName(P)),
        };
        const matching_tag = if (ptr_info.is_const) "immut" else "mut";
        return @unionInit(CtxPtr, matching_tag, @ptrCast(any_ptr));
    }

    pub inline fn toPtr(ctx_ptr: CtxPtr, comptime P: type) P {
        const ptr_info = switch (@typeInfo(P)) {
            .pointer => |ptr_info| ptr_info,
            else => @compileError("Expected pointer, got " ++ @typeName(P)),
        };
        const raw_ptr = @field(ctx_ptr, if (ptr_info.is_const) "immut" else "mut");
        return @alignCast(@ptrCast(raw_ptr));
    }
};

pub const varint = struct {
    pub const encoded_max_len = 1 + @sizeOf(u256);

    pub fn encode(value: u256, buffer: *[encoded_max_len]u8) IntKind {
        const kind: IntKind = .fromValue(value);
        switch (kind) {
            inline .u8, .u16, .u32, .u64, .u128, .u256 => |ikind| {
                const int: ikind.Type() = @intCast(value);
                buffer[0] = if (comptime ikind.firstByte()) |first_byte| first_byte else int;
                if (comptime ikind.remainingLen()) |rem_len| {
                    buffer[1..][0..rem_len].* = @bitCast(int);
                }
            },
        }
        return kind;
    }

    pub fn decodeReader(reader: *std.io.Reader) std.io.Reader.Error!u256 {
        const first_byte = try reader.takeByte();
        const kind: IntKind = .fromFirstByte(first_byte);
        const rem_len = kind.remainingLen() orelse return first_byte;
        const int_bytes = try reader.take(rem_len);
        return kind.decode(int_bytes);
    }

    pub const IntKind = enum {
        /// Encoded in a single byte, with a value from 0 to 250.
        u8,
        /// Encoded as a byte of value 251 followed by a u16.
        u16,
        /// Encoded as a byte of value 252 followed by a u32.
        u32,
        /// Encoded as a byte of value 253 followed by a u64.
        u64,
        /// Encoded as a byte of value 254 followed by a u128.
        u128,
        /// Encoded as a byte of value 255 followed by a u256.
        ///
        /// NOTE: at the time of writing, this is not officially recognized by the specification,
        /// it is only mentioned as being possibly supported in the future with an extension,
        /// under the condition that the corresponding type is added to Rust.
        /// It is included here only for the sake of completeness and algorithmic simplicity.
        u256,

        pub fn Type(comptime kind: IntKind) type {
            return switch (kind) {
                .u8 => u8,
                .u16 => u16,
                .u32 => u32,
                .u64 => u64,
                .u128 => u128,
                .u256 => u256,
            };
        }

        pub fn fromValue(value: u256) IntKind {
            if (value < 251) return .u8;
            if (value < 1 << 16) return .u16;
            if (value < 1 << 32) return .u32;
            if (value < 1 << 64) return .u64;
            if (value < 1 << 128) return .u128;
            if (value < 1 << 256) return .u256;
            comptime unreachable;
        }

        /// Returns null for `.u8`, for which the first byte simply is the value.
        pub fn firstByte(kind: IntKind) ?u8 {
            return switch (kind) {
                .u8 => null,
                .u16 => 251,
                .u32 => 252,
                .u64 => 253,
                .u128 => 254,
                .u256 => 255,
            };
        }

        pub fn fullEncodedLen(kind: IntKind) std.math.IntFittingRange(1, encoded_max_len) {
            return 1 + (kind.remainingLen() orelse 0);
        }

        /// If the return value is `.u8`, `byte` is the entire value.
        pub fn fromFirstByte(first_byte: u8) IntKind {
            return switch (first_byte) {
                0...250 => .u8,
                251 => .u16,
                252 => .u32,
                253 => .u64,
                254 => .u128,
                255 => .u256,
            };
        }

        /// Returns the number of bytes following the first byte which represent the encoded integer,
        /// or null if `kind == .u8`, meaning the first byte is the integer value.
        pub fn remainingLen(kind: IntKind) ?std.math.IntFittingRange(0, encoded_max_len - 1) {
            return switch (kind) {
                .u8 => null,
                .u16 => 2,
                .u32 => 4,
                .u64 => 8,
                .u128 => 16,
                .u256 => 32,
            };
        }

        /// Asserts `kind.remainingLen().? == int_bytes.len`.
        pub fn decode(kind: IntKind, int_bytes: []const u8) u256 {
            std.debug.assert(kind.remainingLen().? == int_bytes.len);
            return switch (kind) {
                .u8 => unreachable,
                inline .u16, .u32, .u64, .u128, .u256 => |ikind| {
                    const T = ikind.Type();
                    const len = comptime ikind.remainingLen().?;
                    const int: T = @bitCast(int_bytes[0..len].*);
                    return int;
                },
            };
        }
    };

    /// Encodes a signed integer as an unsigned integer, such that values
    /// which are closer to zero are mapped to a smaller unsigned integer.
    /// This is used in the varint encoding scheme, where otherwise all
    /// negative values would have a very large encoded representation.
    pub fn zigzag(comptime Signed: type, signed: Signed) Zigzagged(Signed) {
        const unsigned: Zigzagged(Signed) = @bitCast(signed);
        if (signed == 0) return unsigned;
        if (signed > 0) return unsigned * 2;
        if (signed < 0) return ~unsigned * 2 + 1;
        unreachable;
    }

    pub fn Zigzagged(comptime Signed: type) type {
        const signed_info = @typeInfo(Signed).int;
        if (signed_info.signedness != .signed) {
            @compileError("Expected signed integer, got " ++ @typeName(Signed));
        }
        return @Type(.{ .int = .{
            .bits = signed_info.bits,
            .signedness = .unsigned,
        } });
    }

    /// Inverse of `zigzag`.
    pub fn dezigzag(comptime Signed: type, unsigned: Zigzagged(Signed)) Signed {
        if (unsigned == 0) return 0;
        const plus_one_bit: u1 = @intCast(unsigned & 1);
        return switch (plus_one_bit) {
            0 => @bitCast(@divExact(unsigned, 2)),
            1 => @bitCast(~@divExact(unsigned - 1, 2)),
        };
    }
};

test "Codec(u8).byte" {
    var test_reader_buffer: [1]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&test_reader_buffer, &.{.{ .buffer = "foo" }});
    const test_reader = &test_reader_state.interface;

    const byte_codec: Codec(u8) = .byte;

    try std.testing.expectEqual('f', byte_codec.decodeCopy(test_reader));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeCopy(test_reader));
}

test "Codec(bool).byte" {
    var test_reader_buffer: [1]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&test_reader_buffer, &.{.{ .buffer = "\x00\x01\x02" }});
    const test_reader = &test_reader_state.interface;

    const bool_codec: Codec(bool) = .boolean;

    try std.testing.expectEqual(false, bool_codec.decodeCopy(test_reader));
    try std.testing.expectEqual(true, bool_codec.decodeCopy(test_reader));
    try std.testing.expectError(error.DecodeFailed, bool_codec.decodeCopy(test_reader));
    try std.testing.expectError(error.EndOfStream, bool_codec.decodeCopy(test_reader));
}

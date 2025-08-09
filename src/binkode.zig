const std = @import("std");

pub const varint = @import("varint.zig");

pub const IntEncoding = enum {
    varint,
    fixint,
};

pub const Options = struct {
    endian: std.builtin.Endian,
    int: IntEncoding,

    pub const default: Options = .{
        .endian = .little,
        .int = .varint,
    };
};

pub const EncodeError = std.Io.Writer.Error || error{
    /// Codec implementation failed to encode value.
    EncodeFailed,
};

pub const DecodeError = std.Io.Reader.Error || error{
    /// Codec implementation failed to decode value.
    DecodeFailed,
};

/// This represents an encoding & decoding scheme for a value of type `V`,
/// with behaviour defined by callbacks and an optional type-erased context.
///
/// NOTE: many methods in and adjacent to `Codec` are `inline` in order to propagate comptime-knowness.
pub fn Codec(comptime V: type) type {
    return struct {
        /// This is to be used by the codec implementation to modify behaviour, and/or report additional context.
        ctx: Ctx,
        /// Serializes `value.*` to the `writer` stream.
        encodeFn: *const fn (ctx: Ctx, writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void,
        /// Deserializes into `value.*` from the `reader` stream.
        decodeFn: *const fn (ctx: Ctx, reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void,
        const CodecSelf = @This();

        // NOTE: functions here are marked inline in order to preserve the comptime-knowness of
        // `self` and `options`, so that it's easier to devirtualize functionally direct calls.

        pub inline fn encode(
            self: CodecSelf,
            writer: *std.Io.Writer,
            options: Options,
            value: *const V,
        ) EncodeError!void {
            return self.encodeFn(self.ctx, writer, options, value);
        }

        pub inline fn decodeCopy(
            self: CodecSelf,
            reader: *std.Io.Reader,
            options: Options,
        ) DecodeError!V {
            var value: V = undefined;
            try self.decodeInto(reader, options, &value);
            return value;
        }

        pub inline fn decodeInto(
            self: CodecSelf,
            reader: *std.Io.Reader,
            options: Options,
            value: *V,
        ) DecodeError!void {
            return self.decodeFn(self.ctx, reader, options, value);
        }

        // -- Standard Codecs -- //

        /// Standard codec for a byte.
        /// Never fails to encode or decode.
        pub const byte: Codec(u8) = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, _: Options, value: *const u8) EncodeError!void {
                try writer.writeByte(value.*);
            }

            pub fn decode(reader: *std.Io.Reader, _: Options, value: *u8) DecodeError!void {
                value.* = try reader.takeByte();
            }
        });

        /// Standard codec for a boolean.
        /// Failure to decode indicates a byte value other than 0 or 1.
        pub const boolean: Codec(bool) = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, _: Options, value: *const bool) EncodeError!void {
                try writer.writeByte(@intFromBool(value.*));
            }

            pub fn decode(reader: *std.Io.Reader, _: Options, value: *bool) DecodeError!void {
                value.* = switch (try reader.takeByte()) {
                    0 => false,
                    1 => true,
                    else => return error.DecodeFailed,
                };
            }
        });

        /// Standard codec for an integer.
        /// Failure to decode indicates that the value overflowed.
        pub const stdint: CodecSelf = .implementNull(struct {
            const Int = if (V == usize) u64 else V;

            pub fn encode(writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                const int_encoding: IntEncoding = if (is_byte) .fixint else options.int;
                switch (int_encoding) {
                    .fixint => {
                        try writer.writeInt(V, value.*, options.endian);
                    },
                    .varint => {
                        var buffer: [varint.encoded_max_len]u8 = undefined;
                        const int_kind = varint.encode(ifSignedToUnsigned(value.*), &buffer, options.endian);
                        try writer.writeAll(buffer[0..int_kind.fullEncodedLen()]);
                    },
                }
            }

            pub fn decode(reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                const int_encoding: IntEncoding = if (is_byte) .fixint else options.int;
                switch (int_encoding) {
                    .fixint => {
                        const int = try reader.takeInt(Int, options.endian);
                        value.* = std.math.cast(V, int) orelse return error.DecodeFailed;
                    },
                    .varint => {
                        const int = std.math.cast(
                            IfSignedAsUnsigned,
                            try varint.decodeReader(reader, options.endian),
                        ) orelse return error.DecodeFailed;
                        value.* = ifSignedFromUnsigned(int);
                    },
                }
            }

            const int_info = @typeInfo(V).int;
            const is_byte = int_info.bits <= 8;
            const IfSignedAsUnsigned = switch (int_info.signedness) {
                .signed => varint.Zigzagged(V),
                .unsigned => V,
            };
            fn ifSignedToUnsigned(maybe_signed: V) IfSignedAsUnsigned {
                return switch (int_info.signedness) {
                    .signed => varint.zigzag(V, maybe_signed),
                    .unsigned => maybe_signed,
                };
            }
            fn ifSignedFromUnsigned(unsigned: IfSignedAsUnsigned) V {
                return switch (int_info.signedness) {
                    .signed => varint.dezigzag(V, unsigned),
                    .unsigned => unsigned,
                };
            }
        });

        // -- Helpers for safely implementing codecs -- //

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void { ... }
        /// fn decode(reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void { ... }
        /// ```
        /// Returns a stateless codec with the wrapped type-erased encode/decode method callbacks.
        pub inline fn implementNull(comptime methods: type) CodecSelf {
            const erased = struct {
                fn encodeFn(ctx: Ctx, writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                    _ = &ctx.null;
                    try methods.encode(writer, options, value);
                }
                fn decodeFn(ctx: Ctx, reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                    _ = &ctx.null;
                    try methods.decode(reader, options, value);
                }
            };

            return .{
                .ctx = .none,
                .encodeFn = erased.encodeFn,
                .decodeFn = erased.decodeFn,
            };
        }
    };
}

pub const Ctx = union {
    null: void,
    mut: ?*anyopaque,
    immut: ?*const anyopaque,

    pub const none: Ctx = .{ .null = {} };

    pub inline fn fromPtr(any_ptr: anytype) Ctx {
        const P = @TypeOf(any_ptr);
        const ptr_info = switch (@typeInfo(P)) {
            .pointer => |ptr_info| ptr_info,
            else => @compileError("Expected pointer, got " ++ @typeName(P)),
        };
        const matching_tag = if (ptr_info.is_const) "immut" else "mut";
        return @unionInit(Ctx, matching_tag, @ptrCast(any_ptr));
    }

    pub inline fn toPtr(ctx_ptr: Ctx, comptime P: type) P {
        const ptr_info = switch (@typeInfo(P)) {
            .pointer => |ptr_info| ptr_info,
            else => @compileError("Expected pointer, got " ++ @typeName(P)),
        };
        const raw_ptr = @field(ctx_ptr, if (ptr_info.is_const) "immut" else "mut");
        return @ptrCast(@alignCast(raw_ptr));
    }
};

test "Codec(u8).byte" {
    var test_reader_buffer: [4096]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&test_reader_buffer, &.{
        .{ .buffer = "foo" },
    });
    const test_reader = &test_reader_state.interface;

    const byte_codec: Codec(u8) = .byte;

    try std.testing.expectEqual('f', byte_codec.decodeCopy(test_reader, .default));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader, .default));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader, .default));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeCopy(test_reader, .default));
}

test "Codec(bool).byte" {
    var test_reader_buffer: [4096]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&test_reader_buffer, &.{
        .{ .buffer = "\x00\x01\x02" },
    });
    const test_reader = &test_reader_state.interface;

    const bool_codec: Codec(bool) = .boolean;

    try std.testing.expectEqual(false, bool_codec.decodeCopy(test_reader, .default));
    try std.testing.expectEqual(true, bool_codec.decodeCopy(test_reader, .default));
    try std.testing.expectError(error.DecodeFailed, bool_codec.decodeCopy(test_reader, .default));
    try std.testing.expectError(error.EndOfStream, bool_codec.decodeCopy(test_reader, .default));
}

test testStdIntCodec {
    try testStdIntCodec(i8, &.{ 1, 5, 127, 32, 8 });
    try testStdIntCodec(u8, &.{ 1, 5, 255, 32, 8 });
    try testStdIntCodec(i16, &.{ 1, 5, 10000, 32, 8 });
    try testStdIntCodec(u16, &.{ 1, 5, 10000, 32, 8 });
    try testStdIntCodec(i32, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(u32, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(i64, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(u64, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(i128, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(u128, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(i256, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(u256, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(isize, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdIntCodec(usize, &.{ 1, 5, 1000000000, 32, 8 });
}

fn testStdIntCodec(
    comptime T: type,
    ints: []const T,
) !void {
    const int_codec: Codec(T) = .stdint;

    const edge_case_ints = [_]T{
        std.math.minInt(T),

        @max(-1, std.math.minInt(T)),

        0,

        @min(1, std.math.maxInt(T)),

        @min(251 - 1, std.math.maxInt(T)),
        @min(251 + 0, std.math.maxInt(T)),
        @min(251 + 1, std.math.maxInt(T)),

        @min((1 << 16) - 1, std.math.maxInt(T)),
        @min((1 << 16) + 0, std.math.maxInt(T)),
        @min((1 << 16) + 1, std.math.maxInt(T)),

        @min((1 << 32) - 1, std.math.maxInt(T)),
        @min((1 << 32) + 0, std.math.maxInt(T)),
        @min((1 << 32) + 1, std.math.maxInt(T)),

        @min((1 << 64) - 1, std.math.maxInt(T)),
        @min((1 << 64) + 0, std.math.maxInt(T)),
        @min((1 << 64) + 1, std.math.maxInt(T)),

        @min((1 << 128) - 1, std.math.maxInt(T)),
        @min((1 << 128) + 0, std.math.maxInt(T)),
        @min((1 << 128) + 1, std.math.maxInt(T)),

        @min((1 << 256) - 1, std.math.maxInt(T)),
        @min((1 << 256) + 0, std.math.maxInt(T)),
        @min((1 << 256) + 1, std.math.maxInt(T)),

        std.math.maxInt(T),
    };

    const encoded_buffer = try std.testing.allocator.alloc(u8, @max(
        varint.encoded_max_len * (ints.len + edge_case_ints.len),
        @sizeOf(T) * (ints.len + edge_case_ints.len),
    ));
    defer std.testing.allocator.free(encoded_buffer);

    for ([_]Options{
        .{ .int = .varint, .endian = .little },
        .{ .int = .varint, .endian = .big },
        .{ .int = .fixint, .endian = .little },
        .{ .int = .fixint, .endian = .big },
    }) |options| {
        var encoded_writer: std.Io.Writer = .fixed(encoded_buffer);
        for (ints) |int| {
            try int_codec.encode(&encoded_writer, options, &int);
        }
        for (edge_case_ints) |int| {
            try int_codec.encode(&encoded_writer, options, &int);
        }

        var encoded_reader: std.Io.Reader = .fixed(encoded_writer.buffered());
        for (ints) |expected_int| {
            try std.testing.expectEqual(expected_int, int_codec.decodeCopy(&encoded_reader, options));
        }
        for (edge_case_ints) |expected_int| {
            try std.testing.expectEqual(expected_int, int_codec.decodeCopy(&encoded_reader, options));
        }
        try std.testing.expectEqual(0, encoded_reader.bufferedLen());
    }
}

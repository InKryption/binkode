const std = @import("std");

pub const varint = @import("varint.zig");
pub const StdInt = @import("stdint.zig").StdInt;

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
        pub const std_byte: Codec(u8) = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, _: Options, value: *const u8) EncodeError!void {
                try writer.writeByte(value.*);
            }

            pub fn decode(reader: *std.Io.Reader, _: Options, value: *u8) DecodeError!void {
                value.* = try reader.takeByte();
            }
        });

        /// Standard codec for a boolean.
        /// Failure to decode indicates a byte value other than 0 or 1.
        pub const std_bool: Codec(bool) = .implementNull(struct {
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
        pub const std_int: CodecSelf = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                try StdInt(V).encode(writer, options, value.*);
            }

            pub fn decode(reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                value.* = try StdInt(V).decode(reader, options);
            }
        });

        pub const std_float: CodecSelf = .implementNull(struct {
            const AsInt = std.meta.Int(.unsigned, @bitSizeOf(V));

            comptime {
                switch (V) {
                    f32, f64 => {},
                    else => @compileError("float codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                const as_int_endian = std.mem.nativeTo(AsInt, @bitCast(value.*), options.endian);
                try writer.writeAll(@ptrCast(&as_int_endian));
            }

            pub fn decode(reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                try reader.readSliceAll(@ptrCast(value));
                value.* = @bitCast(std.mem.nativeTo(AsInt, @bitCast(value.*), options.endian));
            }
        });

        pub const std_utf8_codepoint: CodecSelf = .implementNull(struct {
            comptime {
                switch (V) {
                    u8, u16, u21, u32 => {},
                    else => @compileError("char codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(writer: *std.Io.Writer, _: Options, value: *const V) EncodeError!void {
                if (value.* > std.math.maxInt(u21)) return error.EncodeFailed;
                const cp_val: u21 = @intCast(value.*);
                const cp_len = std.unicode.utf8CodepointSequenceLength(cp_val) catch
                    return error.EncodeFailed;
                var encoded_buffer: [4]u8 = undefined;
                const encoded = encoded_buffer[0..cp_len];
                std.unicode.utf8Encode(cp_val, encoded) catch return error.EncodeFailed;
                try writer.writeAll(encoded);
            }

            pub fn decode(reader: *std.Io.Reader, _: Options, value: *V) DecodeError!void {
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
                value.* = switch (cp_len) {
                    1 => value[0],
                    2 => std.unicode.utf8Decode2(encoded[0..2].*),
                    3 => std.unicode.utf8Decode3(encoded[0..3].*),
                    4 => std.unicode.utf8Decode4(encoded[0..4].*),
                    else => unreachable,
                } catch return error.DecodeFailed;
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

    const byte_codec: Codec(u8) = .std_byte;

    try std.testing.expectEqual('f', byte_codec.decodeCopy(test_reader, .default));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader, .default));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader, .default));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeCopy(test_reader, .default));
}

test "Codec(bool).bool" {
    var test_reader_buffer: [4096]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&test_reader_buffer, &.{
        .{ .buffer = "\x00\x01\x02" },
    });
    const test_reader = &test_reader_state.interface;

    const bool_codec: Codec(bool) = .std_bool;

    try std.testing.expectEqual(false, bool_codec.decodeCopy(test_reader, .default));
    try std.testing.expectEqual(true, bool_codec.decodeCopy(test_reader, .default));
    try std.testing.expectError(error.DecodeFailed, bool_codec.decodeCopy(test_reader, .default));
    try std.testing.expectError(error.EndOfStream, bool_codec.decodeCopy(test_reader, .default));
}

test testStdIntCodec {
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
    const min_int = std.math.minInt(T);
    const max_int = std.math.maxInt(T);
    try testCodecRoundTrips(T, .std_int, ints);
    try testCodecRoundTrips(T, .std_int, &.{
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
    });
}

test testStdFloatCodec {
    try testStdFloatCodec(f32, &.{ 1, 5, 10000, 32, 8 });
    try testStdFloatCodec(f32, &.{ 1, 5, 1000000000, 32, 8 });
    try testStdFloatCodec(f64, &.{ 1, 5, 10000, 32, 8 });
    try testStdFloatCodec(f64, &.{ 1, 5, 1000000000, 32, 8 });
}

fn testStdFloatCodec(
    comptime T: type,
    floats: []const T,
) !void {
    const inf = std.math.inf(T);
    const max = std.math.floatMax(T);
    const eps = std.math.floatEps(T);
    const min = std.math.floatMin(T);
    const min_true = std.math.floatTrueMin(T);

    try testCodecRoundTrips(T, .std_float, floats);
    try testCodecRoundTrips(T, .std_float, &.{
        0.0,      -0.0,
        min_true, -min_true,
        min,      -min,
        0.1,      -0.1,
        0.2,      -0.2,
        0.3,      -0.3,
        eps,      -eps,
        max,      -max,
        inf,      -inf,
    });
}

fn testCodecRoundTrips(
    comptime T: type,
    codec: Codec(T),
    values: []const T,
) !void {
    var buffer: std.ArrayListUnmanaged(u8) = .empty;
    defer buffer.deinit(std.testing.allocator);

    const opt_permutations = [_]Options{
        .{ .int = .varint, .endian = .little },
        .{ .int = .varint, .endian = .big },
        .{ .int = .fixint, .endian = .little },
        .{ .int = .fixint, .endian = .big },
    };
    for (opt_permutations) |options| {
        {
            buffer.clearRetainingCapacity();
            var encoded_writer_state: std.Io.Writer.Allocating = .fromArrayList(std.testing.allocator, &buffer);
            defer buffer = encoded_writer_state.toArrayList();
            const encoded_writer: *std.Io.Writer = &encoded_writer_state.writer;
            for (values) |int| try codec.encode(encoded_writer, options, &int);
        }

        var encoded_reader: std.Io.Reader = .fixed(buffer.items);
        for (values) |expected_int| {
            try std.testing.expectEqual(expected_int, codec.decodeCopy(&encoded_reader, options));
        }
        try std.testing.expectEqual(0, encoded_reader.bufferedLen());
    }
}

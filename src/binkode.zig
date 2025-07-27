const std = @import("std");

pub const varint = @import("varint.zig");

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
        ctx: Ctx,
        /// Serializes `value.*` to the `writer` stream.
        encodeFn: *const fn (ctx: Ctx, writer: *std.Io.Writer, value: *const V) EncodeError!void,
        /// Deserializes into `value.*` from the `reader` stream.
        decodeFn: *const fn (ctx: Ctx, reader: *std.Io.Reader, value: *V) DecodeError!void,
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
        pub const byte: Codec(u8) = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, value: *const u8) EncodeError!void {
                try writer.writeByte(value.*);
            }
            pub fn decode(reader: *std.Io.Reader, value: *u8) DecodeError!void {
                value.* = try reader.takeByte();
            }
        });

        /// Standard codec for a boolean.
        /// Failure to decode indicates a byte value other than 0 or 1.
        pub const boolean: Codec(bool) = .implementNull(struct {
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

        /// Standard codec for fix-encoded integer.
        /// Failure to decode indicates overflow for the destination type.
        pub fn fixInt(encoded_endian: std.builtin.Endian) CodecSelf {
            const Int = if (V == usize) u64 else V;
            return .implementEndian(encoded_endian, struct {
                pub fn encode(endian: std.builtin.Endian, writer: *std.Io.Writer, value: *const V) EncodeError!void {
                    try writer.writeInt(Int, value.*, endian);
                }
                pub fn decode(endian: std.builtin.Endian, reader: *std.Io.Reader, value: *V) DecodeError!void {
                    const int = try reader.takeInt(Int, endian);
                    value.* = std.math.cast(V, int) orelse return error.DecodeFailed;
                }
            });
        }

        /// Standard codec for variably-encoded integer.
        /// Failure to decode indicates overflow for the destination type.
        pub fn varInt(encoded_endian: std.builtin.Endian) CodecSelf {
            if (@bitSizeOf(V) <= 8) @compileError("Bytes should use `.byte`");
            return .implementEndian(encoded_endian, struct {
                pub fn encode(endian: std.builtin.Endian, writer: *std.Io.Writer, value: *const V) EncodeError!void {
                    var buffer: [varint.encoded_max_len]u8 = undefined;
                    const int_kind = varint.encode(ifSignedToUnsigned(value.*), &buffer, endian);
                    try writer.writeAll(buffer[0..int_kind.fullEncodedLen()]);
                }
                pub fn decode(endian: std.builtin.Endian, reader: *std.Io.Reader, value: *V) DecodeError!void {
                    const int = std.math.cast(
                        IfSignedAsUnsigned,
                        try varint.decodeReader(reader, endian),
                    ) orelse return error.DecodeFailed;
                    value.* = ifSignedFromUnsigned(int);
                }

                const int_info = @typeInfo(V).int;
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
        }

        // -- Helpers for safely implementing codecs -- //

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, value: *const V) EncodeError!void { ... }
        /// fn decode(reader: *std.Io.Reader, value: *V) DecodeError!void { ... }
        /// ```
        /// Returns a stateless codec with the wrapped type-erased encode/decode method callbacks.
        pub inline fn implementNull(comptime methods: type) CodecSelf {
            const erased = struct {
                fn encodeFn(ctx: Ctx, writer: *std.Io.Writer, value: *const V) EncodeError!void {
                    _ = &ctx.null;
                    try methods.encode(writer, value);
                }
                fn decodeFn(ctx: Ctx, reader: *std.Io.Reader, value: *V) DecodeError!void {
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

        // -- Helpers for safely implementing codecs -- //

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(endian: std.builtin.Endian, writer: *std.Io.Writer, value: *const V) EncodeError!void { ... }
        /// fn decode(endian: std.builtin.Endian, reader: *std.Io.Reader, value: *V) DecodeError!void { ... }
        /// ```
        /// Returns a codec defined to encode using the specified endian parameter.
        pub inline fn implementEndian(endian: std.builtin.Endian, comptime methods: type) CodecSelf {
            const erased = struct {
                fn encodeFn(ctx: Ctx, writer: *std.Io.Writer, value: *const V) EncodeError!void {
                    try methods.encode(ctx.endian, writer, value);
                }
                fn decodeFn(ctx: Ctx, reader: *std.Io.Reader, value: *V) DecodeError!void {
                    try methods.decode(ctx.endian, reader, value);
                }
            };

            return .{
                .ctx = .fromEndian(endian),
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
                fn encodeFn(ctx: Ctx, writer: *std.Io.Writer, value: *const V) EncodeError!void {
                    try ctx.toPtr(CtxImpl).encode(writer, value);
                }
                fn decodeFn(ctx: Ctx, reader: *std.Io.Reader, value: *V) DecodeError!void {
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

pub const Ctx = union {
    null: void,
    endian: std.builtin.Endian,
    mut: *anyopaque,
    immut: *const anyopaque,

    pub const none: Ctx = .{ .null = {} };

    pub fn fromEndian(endian: std.builtin.Endian) Ctx {
        return .{ .endian = endian };
    }

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
        return @alignCast(@ptrCast(raw_ptr));
    }
};

test "Codec(u8).byte" {
    var test_reader_buffer: [4096]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&test_reader_buffer, &.{.{ .buffer = "foo" }});
    const test_reader = &test_reader_state.interface;

    const byte_codec: Codec(u8) = .byte;

    try std.testing.expectEqual('f', byte_codec.decodeCopy(test_reader));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader));
    try std.testing.expectEqual('o', byte_codec.decodeCopy(test_reader));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeCopy(test_reader));
}

test "Codec(bool).byte" {
    var test_reader_buffer: [4096]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&test_reader_buffer, &.{.{ .buffer = "\x00\x01\x02" }});
    const test_reader = &test_reader_state.interface;

    const bool_codec: Codec(bool) = .boolean;

    try std.testing.expectEqual(false, bool_codec.decodeCopy(test_reader));
    try std.testing.expectEqual(true, bool_codec.decodeCopy(test_reader));
    try std.testing.expectError(error.DecodeFailed, bool_codec.decodeCopy(test_reader));
    try std.testing.expectError(error.EndOfStream, bool_codec.decodeCopy(test_reader));
}

test testFixIntCodec {
    try testFixIntCodec(.little, u64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });
    try testFixIntCodec(.big, u64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });

    try testFixIntCodec(.little, i64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });
    try testFixIntCodec(.big, i64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });

    try testFixIntCodec(.little, u16, &.{std.math.maxInt(u16)});
    try testFixIntCodec(.big, u16, &.{std.math.maxInt(u16)});

    try testFixIntCodec(.little, i16, &.{ std.math.minInt(i16), std.math.maxInt(i16) });
    try testFixIntCodec(.big, i16, &.{ std.math.minInt(i16), std.math.maxInt(i16) });

    var prng_state: std.Random.DefaultPrng = .init(16724);
    const prng = prng_state.random();
    try testFixIntCodec(.little, u32, &.{ prng.int(u32), prng.int(u32), prng.int(u32), prng.int(u32) });
    try testFixIntCodec(.big, i32, &.{ prng.int(i32), prng.int(i32), prng.int(i32), prng.int(i32) });
}

fn testFixIntCodec(
    endian: std.builtin.Endian,
    comptime T: type,
    ints: []const T,
) !void {
    const fixint_codec: Codec(T) = .fixInt(endian);

    const fws_buffer = try std.testing.allocator.alloc(u8, ints.len * @sizeOf(T));
    defer std.testing.allocator.free(fws_buffer);
    var fixed_w: std.io.Writer = .fixed(fws_buffer);

    for (ints) |int| {
        try fixint_codec.encode(&fixed_w, &int);
    }

    var buffer: [4096]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&buffer, &.{
        .{ .buffer = fixed_w.buffered() },
    });
    const test_reader = &test_reader_state.interface;

    for (ints) |expected_int| {
        try std.testing.expectEqual(
            expected_int,
            fixint_codec.decodeCopy(test_reader),
        );
    }
    try std.testing.expectError(
        error.EndOfStream,
        fixint_codec.decodeCopy(test_reader),
    );
}

test testVarIntCodec {
    try testFixIntCodec(.little, u64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });
    try testFixIntCodec(.big, u64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });

    try testFixIntCodec(.little, i64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });
    try testFixIntCodec(.big, i64, &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 });

    try testFixIntCodec(.little, u16, &.{std.math.maxInt(u16)});
    try testFixIntCodec(.big, u16, &.{std.math.maxInt(u16)});

    try testFixIntCodec(.little, i16, &.{ std.math.minInt(i16), std.math.maxInt(i16) });
    try testFixIntCodec(.big, i16, &.{ std.math.minInt(i16), std.math.maxInt(i16) });

    var prng_state: std.Random.DefaultPrng = .init(16724);
    const prng = prng_state.random();
    try testFixIntCodec(.little, u32, &.{ prng.int(u32), prng.int(u32), prng.int(u32), prng.int(u32) });
    try testFixIntCodec(.big, i32, &.{ prng.int(i32), prng.int(i32), prng.int(i32), prng.int(i32) });
}

fn testVarIntCodec(
    endian: std.builtin.Endian,
    comptime T: type,
    ints: []const T,
) !void {
    const varint_codec: Codec(T) = .varInt(endian);

    const fws_buffer = try std.testing.allocator.alloc(u8, ints.len * @sizeOf(T));
    defer std.testing.allocator.free(fws_buffer);
    var fixed_w: std.io.Writer = .fixed(fws_buffer);

    for (ints) |int| {
        try varint_codec.encode(&fixed_w, &int);
    }

    var buffer: [4096]u8 = undefined;
    var test_reader_state: std.testing.Reader = .init(&buffer, &.{
        .{ .buffer = fixed_w.buffered() },
    });
    const test_reader = &test_reader_state.interface;

    for (ints) |expected_int| {
        try std.testing.expectEqual(
            expected_int,
            varint_codec.decodeCopy(test_reader),
        );
    }
    try std.testing.expectError(
        error.EndOfStream,
        varint_codec.decodeCopy(test_reader),
    );
}

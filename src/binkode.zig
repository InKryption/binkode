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

        pub const Ctx = union {
            null: void,
            mut: ?*anyopaque,
            immut: ?*const anyopaque,
            payload: if (Payload == noreturn) noreturn else *const Payload,
            fields: if (Fields == noreturn) noreturn else *const Fields,

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

            pub const Payload = switch (@typeInfo(V)) {
                .optional => |optional_info| Codec(optional_info.child),
                else => noreturn,
            };

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
                                .type = FieldCodec,
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
        };

        // -- Standard Codecs -- //

        /// Standard codec for a zero-sized value.
        pub const std_void: CodecSelf = .implementNull(struct {
            comptime {
                if (@sizeOf(V) != 0) @compileError(
                    "void codec is not implemented for type " ++ @typeName(V) ++
                        " of size " ++ std.fmt.comptimePrint("{d}", .{@sizeOf(V)}),
                );
            }

            pub fn encode(writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                _ = writer;
                _ = options;
                _ = value;
            }

            pub fn decode(reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                _ = reader;
                _ = options;
                _ = value;
            }
        });

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

        /// Standard codec for a float.
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

        /// Standard codec for a UTF-8 codepoint.
        /// Failure to encode indicates an invalid codepoint value.
        /// Failure to decode indicates an invalid codepoint value.
        pub const std_utf8_codepoint: CodecSelf = .implementNull(struct {
            comptime {
                switch (V) {
                    u1, u2, u3, u4, u5, u6, u7 => {},
                    u8, u16, u21, u32 => {},
                    else => @compileError("char codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(writer: *std.Io.Writer, _: Options, value: *const V) EncodeError!void {
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
        });

        /// Standard codec for an optional.
        /// Failure to decode indicates either a failure to decode the boolean, or the potential payload.
        pub inline fn stdOptional(payload_codec: *const Ctx.Payload) CodecSelf {
            return .implementPayload(payload_codec, struct {
                const Unwrapped = @typeInfo(V).optional.child;

                pub fn encode(pl_codec: Ctx.Payload, writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                    try std_bool.encode(writer, options, &(value.* != null));
                    const payload = if (value.*) |*unwrapped| unwrapped else return;
                    try pl_codec.encode(writer, options, payload);
                }

                pub fn decode(pl_codec: Ctx.Payload, reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                    const is_some = try std_bool.decodeCopy(reader, options);
                    value.* = if (is_some) @as(Unwrapped, undefined) else null;
                    if (is_some) try pl_codec.decodeInto(reader, options, &value.*.?);
                }
            });
        }

        /// Standard codec for a struct.
        pub inline fn stdStruct(field_codecs: *const Ctx.Fields) CodecSelf {
            return .implementFields(field_codecs, struct {
                pub fn encode(
                    fields: Ctx.Fields,
                    writer: *std.Io.Writer,
                    options: Options,
                    value: *const V,
                ) EncodeError!void {
                    inline for (@typeInfo(V).@"struct".fields) |s_field| {
                        const field_codec: Codec(s_field.type) = @field(fields, s_field.name);
                        try field_codec.encode(writer, options, &@field(value, s_field.name));
                    }
                }

                pub fn decode(
                    fields: Ctx.Fields,
                    reader: *std.Io.Reader,
                    options: Options,
                    value: *V,
                ) DecodeError!void {
                    inline for (@typeInfo(V).@"struct".fields) |s_field| {
                        const field_codec: Codec(s_field.type) = @field(fields, s_field.name);
                        try field_codec.decodeInto(reader, options, &@field(value, s_field.name));
                    }
                }
            });
        }

        /// Standard codec for a tagged union, aka "enums" in the bincode specification, written in the context of rust.
        /// Also see: `std_discriminant`.
        pub inline fn stdUnion(field_contexts: *const Ctx.Fields) CodecSelf {
            return .implementFields(field_contexts, struct {
                const union_info = @typeInfo(V).@"union";
                const tag_codec: Codec(union_info.tag_type.?) = .std_discriminant;

                pub fn encode(
                    field_codecs: Ctx.Fields,
                    writer: *std.Io.Writer,
                    options: Options,
                    value: *const V,
                ) EncodeError!void {
                    const tag: union_info.tag_type.? = value.*;
                    try tag_codec.encode(writer, options, &tag);
                    switch (value.*) {
                        inline else => |*payload, itag| {
                            const Payload = @TypeOf(payload.*);
                            const field_codec: Codec(Payload) = @field(field_codecs, @tagName(itag));
                            try field_codec.encode(writer, options, payload);
                        },
                    }
                }

                pub fn decode(
                    payload_codecs: Ctx.Fields,
                    reader: *std.Io.Reader,
                    options: Options,
                    value: *V,
                ) DecodeError!void {
                    switch (try tag_codec.decodeCopy(reader, options)) {
                        inline else => |itag| {
                            value.* = @unionInit(V, @tagName(itag), undefined);
                            const Payload = @FieldType(V, @tagName(itag));
                            const payload_codec: Codec(Payload) = @field(payload_codecs, @tagName(itag));
                            try payload_codec.decodeInto(reader, options, &@field(value, @tagName(itag)));
                        },
                    }
                }
            });
        }

        /// Standard codec for an enum used as a discriminant, aka the tag of a tagged union, aka the tag of a rust enum.
        /// Failure to decode indicates the value overflowed or didn't match a valid value.
        pub const std_discriminant: CodecSelf = .implementNull(struct {
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

            pub fn encode(writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                const as_u32: u32 = @intFromEnum(value.*);
                return Codec(u32).std_int.encode(writer, options, &as_u32);
            }

            pub fn decode(reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                const as_u32 = try Codec(u32).std_int.decodeCopy(reader, options);
                if (as_u32 > std.math.maxInt(enum_info.tag_type)) return error.DecodeFailed;
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
                value.* = std.enums.fromInt(V, raw) orelse return error.DecodeFailed;
            }
        });

        // -- Helpers for safely implementing codecs -- //

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(payload_codec: Codec(Payload), writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void { ... }
        /// fn decode(payload_codec: Codec(Payload), reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void { ... }
        /// ```
        pub inline fn implementPayload(payload: *const Ctx.Payload, comptime methods: type) CodecSelf {
            const erased = struct {
                fn encodeFn(ctx: Ctx, writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                    try methods.encode(ctx.payload.*, writer, options, value);
                }
                fn decodeFn(ctx: Ctx, reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                    try methods.decode(ctx.payload.*, reader, options, value);
                }
            };

            return .{
                .ctx = .{ .payload = payload },
                .encodeFn = erased.encodeFn,
                .decodeFn = erased.decodeFn,
            };
        }

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(fields_codec: CodecSelf.Ctx.Fields, writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void { ... }
        /// fn decode(fields_codec: CodecSelf.Ctx.Fields, reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void { ... }
        /// ```
        pub inline fn implementFields(fields: *const Ctx.Fields, comptime methods: type) CodecSelf {
            const erased = struct {
                fn encodeFn(ctx: Ctx, writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void {
                    try methods.encode(ctx.fields.*, writer, options, value);
                }
                fn decodeFn(ctx: Ctx, reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void {
                    try methods.decode(ctx.fields.*, reader, options, value);
                }
            };

            return .{
                .ctx = .{ .fields = fields },
                .encodeFn = erased.encodeFn,
                .decodeFn = erased.decodeFn,
            };
        }

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, options: Options, value: *const V) EncodeError!void { ... }
        /// fn decode(reader: *std.Io.Reader, options: Options, value: *V) DecodeError!void { ... }
        /// ```
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

test "std_void" {
    var null_reader: std.Io.Reader = .failing;
    var null_writer: std.Io.Writer.Discarding = .init(&.{});
    const void_codec: Codec(void) = .std_void;
    try std.testing.expectEqual({}, void_codec.encode(&null_writer.writer, .default, &{}));
    try std.testing.expectEqual({}, void_codec.decodeCopy(&null_reader, .default));
}

test "std_byte" {
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

test "std_bool" {
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

test "std_int" {
    try testCodecRoundTrips(i16, .std_int, &intTestEdgeCases(i16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(u16, .std_int, &intTestEdgeCases(u16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(i32, .std_int, &intTestEdgeCases(i32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u32, .std_int, &intTestEdgeCases(u32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i64, .std_int, &intTestEdgeCases(i64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u64, .std_int, &intTestEdgeCases(u64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i128, .std_int, &intTestEdgeCases(i128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u128, .std_int, &intTestEdgeCases(u128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i256, .std_int, &intTestEdgeCases(i256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u256, .std_int, &intTestEdgeCases(u256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(isize, .std_int, &intTestEdgeCases(isize) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(usize, .std_int, &intTestEdgeCases(usize) ++ .{ 1, 5, 1000000000, 32, 8 });
}

test "std_float" {
    try testCodecRoundTrips(f32, .std_float, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f32, .std_float, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f64, .std_float, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f64, .std_float, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f32, .std_float, &floatTestEdgeCases(f32));
    try testCodecRoundTrips(f64, .std_float, &floatTestEdgeCases(f64));
}

test "std_utf8_codepoint" {
    try testCodecRoundTrips(u8, .std_utf8_codepoint, &@as([128]u8, std.simd.iota(u8, 128))); // ascii
    inline for (.{ u1, u2, u3, u4, u5, u6, u7, u8, u16, u21, u32 }) |AsciiInt| {
        const max_val = @min(127, std.math.maxInt(AsciiInt));
        const ascii_vals: [max_val + 1]AsciiInt = std.simd.iota(AsciiInt, max_val + 1);
        try testCodecRoundTrips(
            AsciiInt,
            .std_utf8_codepoint,
            &ascii_vals,
        );
    }
    try testCodecRoundTrips(u21, .std_utf8_codepoint, &.{ 'à', 'á', 'é', 'è', 'ì', 'í', 'ò', 'ó', 'ù', 'ú' });
    try testCodecRoundTrips(u21, .std_utf8_codepoint, &.{ '\u{2100}', '\u{3100}', '\u{FFAAA}', '\u{FFFFF}', '\u{FFFFF}' });
}

test "stdOptional" {
    try testCodecRoundTrips(?void, .stdOptional(&.std_void), &.{ null, {}, null, {}, null, {} });
    try testCodecRoundTrips(?bool, .stdOptional(&.std_bool), &.{
        null, false, null, true, null, true,
        null, false, true, true, null, false,
    });
    try testCodecRoundTrips(?u32, .stdOptional(&.std_int), &.{ null, 4, null, 10000, null, 100000000 });
    try testCodecRoundTrips(?i64, .stdOptional(&.std_int), &.{ null, -7, null, 20000, null, -100000000 });
}

test "stdStruct" {
    const S = struct {
        a: u32,
        b: f64,
    };
    const struct_codec: Codec(S) = .stdStruct(&.{
        .a = .std_int,
        .b = .std_float,
    });

    const struct_test_edge_cases = comptime blk: {
        const ints = intTestEdgeCases(u32);
        const floats = floatTestEdgeCases(f64);
        var struct_test_edge_cases: [ints.len * floats.len]S = undefined;

        for (ints, 0..) |int, i| for (floats, 0..) |float, j| {
            struct_test_edge_cases[i + j * ints.len] = .{ .a = int, .b = float };
        };

        break :blk struct_test_edge_cases;
    };
    try testCodecRoundTrips(S, struct_codec, &struct_test_edge_cases);
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
    };
    const union_codec: Codec(U) = .stdUnion(&.{
        .void = .std_void,
        .char = .std_byte,
        .int = .std_int,
        .float = .std_float,
        .record = .stdStruct(&.{
            .a = .std_int,
            .b = .std_int,
            .c = .std_discriminant,
        }),
    });

    try testCodecRoundTrips(U, union_codec, &.{
        .void,
        .{ .char = 42 },
        .{ .int = 1111111111 },
        .{ .float = -7 },
        .{ .record = .{ .a = 1, .b = 2, .c = .foo } },
    });
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

const std = @import("std");
const bk = @import("binkode.zig");

const testing = @import("testing.zig");

pub fn StdCodec(comptime V: type) type {
    return struct {
        codec: Base,
        const StdCodecSelf = @This();

        pub const Base = bk.Codec(V);

        /// Wrap a normal base codec. Useful for composing multiple codecs,
        /// both standard and non-standard.
        pub fn from(base: Base) StdCodecSelf {
            return .{ .codec = base };
        }

        /// Standard codec for a zero-sized value.
        /// Never fails to encode or decode.
        pub const empty: StdCodecSelf = .from(.implement(void, void, struct {
            comptime {
                if (@sizeOf(V) != 0) @compileError(
                    "void codec is not implemented for type " ++ @typeName(V) ++
                        " of size " ++ std.fmt.comptimePrint("{d}", .{@sizeOf(V)}),
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                values: []const V,
                progress_stack: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                ctx: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                _ = progress_stack;
                _ = limit;
                _ = writer;
                _ = config;
                _ = ctx;
                return .{
                    .value_count = values.len,
                    .byte_count = 0,
                };
            }

            pub const encode_min_size: usize = 0;

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                gpa_opt: ?std.mem.Allocator,
                values: []V,
                decoded_count: *usize,
                ctx: void,
            ) bk.DecodeFromReaderError!void {
                _ = reader;
                _ = config;
                _ = gpa_opt;
                _ = ctx;
                decoded_count.* = values.len;
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                config: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                ctx: void,
            ) bk.DecodeSkipError!void {
                _ = reader;
                _ = config;
                _ = ctx;
                decoded_count.* = value_count;
            }

            pub const free = null;
        }));

        /// Standard codec for a byte.
        /// Never fails to encode or decode.
        pub const byte: StdCodec(u8) = .from(.implement(void, void, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                _: bk.Config,
                values: []const u8,
                _: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                const bytes_to_write = limit.sliceConst(values);
                try writer.writeAll(bytes_to_write);
                return .{
                    .value_count = bytes_to_write.len,
                    .byte_count = bytes_to_write.len,
                };
            }

            pub const encode_min_size: usize = 1;

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: bk.Config,
                _: ?std.mem.Allocator,
                values: []u8,
                decoded_count: *usize,
                _: void,
            ) bk.DecodeFromReaderError!void {
                try reader.readSliceAll(values);
                decoded_count.* = values.len;
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                _: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                _: void,
            ) bk.DecodeSkipError!void {
                try reader.discardAll(value_count);
                decoded_count.* = value_count;
            }

            pub const free = null;
        }));

        pub const BoolDecodeDiag = struct {
            /// Value of the actual decoded byte with an erroneous value.
            /// Only set to non-null if `error.DecodeFailed` is returned.
            real_byte: ?u8,

            pub const init: BoolDecodeDiag = .{ .real_byte = null };
        };

        /// Standard codec for a boolean.
        /// Never fails to encode.
        /// Failure to decode indicates a byte value other than 0 or 1.
        /// Decode's initial state is write-only.
        pub const boolean: StdCodec(bool) = .from(.implement(void, ?*BoolDecodeDiag, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                values: []const bool,
                progress_stack: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                comptime if (@sizeOf(bool) != @sizeOf(u8)) unreachable;
                return try byte.codec.encodeManyPartialRaw(
                    writer,
                    config,
                    @ptrCast(values),
                    progress_stack,
                    limit,
                    {},
                );
            }

            pub const encode_min_size: usize = byte.codec.encode_min_size;

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: bk.Config,
                _: ?std.mem.Allocator,
                values: []bool,
                decoded_count: *usize,
                maybe_diag: ?*BoolDecodeDiag,
            ) bk.DecodeFromReaderError!void {
                decoded_count.* = values.len;
                for (values, 0..) |*value, i| {
                    errdefer decoded_count.* = i;

                    value.* = switch (try readOneByte(reader)) {
                        0 => false,
                        1 => true,
                        else => |real_byte| {
                            if (maybe_diag) |diag| diag.real_byte = real_byte;
                            return error.DecodeFailed;
                        },
                    };
                }
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                _: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                maybe_diag: ?*BoolDecodeDiag,
            ) bk.DecodeSkipError!void {
                decoded_count.* = value_count;
                for (0..value_count) |i| {
                    errdefer decoded_count.* = i;

                    switch (try readOneByte(reader)) {
                        0, 1 => {},
                        else => |real_byte| {
                            if (maybe_diag) |diag| diag.real_byte = real_byte;
                            return error.DecodeFailed;
                        },
                    }
                }
            }

            fn readOneByte(reader: *std.Io.Reader) std.Io.Reader.Error!u8 {
                var real_byte: u8 = undefined;
                try reader.readSliceAll((&real_byte)[0..1]);
                return real_byte;
            }

            pub const free = null;
        }));

        pub const IntDecodeDiag = struct {
            /// Value of the actual decoded raw integer with an erroneous value.
            /// Only set when `error.DecodeFailed` is returned.
            raw_int: ?switch (@typeInfo(V).int.signedness) {
                .unsigned => u256,
                .signed => i256,
            },

            pub const init: IntDecodeDiag = .{ .raw_int = null };
        };

        /// Standard codec for an integer representing a length.
        /// Also see:
        /// * `int`
        pub const length: StdCodec(usize) = .int;

        /// Standard codec for an integer. Encodes `usize` and `isize` as `u64` and `i64`, respectively.
        /// Never fails to encode.
        /// Failure to decode indicates that the value overflowed.
        /// Decode's initial state is write-only.
        pub const int: StdCodecSelf = .from(.implement(void, ?*IntDecodeDiag, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                values: []const V,
                _: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                switch (config.int) {
                    inline .fixint, .varint => |mode| {
                        const int_codec: bk.Codec(V) = switch (mode) {
                            .fixint => fixint.codec,
                            .varint => varint.codec,
                        };
                        return try int_codec.encodeManyPartialRaw(writer, config, values, null, limit, {});
                    },
                }
            }

            pub const encode_min_size: usize = @max(
                fixint.codec.encode_min_size,
                varint.codec.encode_min_size,
            );

            pub const encode_stack_size: usize = @max(
                fixint.codec.encode_stack_size,
                varint.codec.encode_stack_size,
            );

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                values: []V,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) bk.DecodeFromReaderError!void {
                try decodeImpl(reader, config, false, values, decoded_count, maybe_diag);
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                config: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) bk.DecodeSkipError!void {
                try decodeImpl(reader, config, true, value_count, decoded_count, maybe_diag);
            }

            fn decodeImpl(
                reader: *std.Io.Reader,
                config: bk.Config,
                comptime skip: bool,
                values_or_count: if (skip) usize else []V,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) !void {
                switch (config.int) {
                    inline .fixint, .varint => |which| {
                        const int_codec: Base = comptime switch (which) {
                            .fixint => fixint.codec,
                            .varint => varint.codec,
                        };
                        if (!skip) {
                            try int_codec.decodeIntoManyRaw(
                                reader,
                                null,
                                config,
                                values_or_count,
                                decoded_count,
                                maybe_diag,
                            );
                        } else {
                            try int_codec.decodeSkipManyRaw(
                                reader,
                                config,
                                values_or_count,
                                decoded_count,
                                maybe_diag,
                            );
                        }
                    },
                }
            }

            pub const free = null;
        }));

        pub const fixint: StdCodecSelf = .from(.implement(void, ?*IntDecodeDiag, struct {
            const Int = switch (V) {
                usize => u64,
                isize => i64,
                else => V,
            };

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                values: []const V,
                _: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                if (Int != V) {
                    const int_endian: Int = std.mem.nativeTo(Int, values[0], config.endian);
                    const as_bytes: []const u8 = @ptrCast(&int_endian);
                    if (limit.toInt()) |byte_limit| {
                        std.debug.assert(byte_limit >= as_bytes.len);
                    }
                    try writer.writeAll(as_bytes);
                    return .{
                        .value_count = 1,
                        .byte_count = as_bytes.len,
                    };
                } else {
                    const values_end: usize, const bytes_end: usize = blk: {
                        const values_byte_count = values.len * @sizeOf(Int);
                        const byte_limit = limit.toInt() orelse
                            break :blk .{ values.len, values_byte_count };
                        if (byte_limit >= values_byte_count) {
                            break :blk .{ values.len, values_byte_count };
                        }
                        const byte_limit_aligned = std.mem.alignBackward(usize, byte_limit, @sizeOf(Int));
                        break :blk .{ @divExact(byte_limit_aligned, @sizeOf(Int)), byte_limit_aligned };
                    };

                    try writer.writeSliceEndian(Int, values[0..values_end], config.endian);
                    return .{
                        .value_count = values_end,
                        .byte_count = bytes_end,
                    };
                }
            }

            pub const encode_min_size: usize = @sizeOf(Int);

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                values: []V,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) bk.DecodeFromReaderError!void {
                try decodeImpl(reader, config, false, values, decoded_count, maybe_diag);
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                config: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) bk.DecodeSkipError!void {
                try decodeImpl(reader, config, true, value_count, decoded_count, maybe_diag);
            }

            fn decodeImpl(
                reader: *std.Io.Reader,
                config: bk.Config,
                comptime skip: bool,
                values_or_count: if (skip) usize else []V,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) !void {
                const value_count: usize = if (skip) values_or_count else values_or_count.len;
                const values = if (skip) blk: {
                    var void_slice: []void = &.{};
                    void_slice.len = value_count;
                    break :blk void_slice;
                } else values_or_count;

                decoded_count.* = value_count;
                for (values, 0..value_count) |*value, index| {
                    errdefer decoded_count.* = index;

                    var int_bytes: [@sizeOf(Int)]u8 = undefined;
                    try reader.readSliceAll(&int_bytes);
                    const decoded_int = std.mem.readInt(Int, &int_bytes, config.endian);
                    if (std.math.minInt(V) > decoded_int or decoded_int > std.math.maxInt(V)) {
                        if (maybe_diag) |diag| diag.raw_int = decoded_int;
                        decoded_count.* = index;
                        return error.DecodeFailed;
                    }
                    if (!skip) value.* = @intCast(decoded_int);
                }
            }

            pub const free = null;
        }));

        pub const varint: StdCodecSelf = .from(.implement(void, ?*IntDecodeDiag, struct {
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
                config: bk.Config,
                values: []const V,
                _: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                if (limit.toInt()) |byte_limit| {
                    const unsigned_int = bk.varint.zigzag.anyToUnsigned(Int, values[0]);
                    var buffer: [bk.varint.IntKind.fullEncodedLen(.maximum)]u8 = undefined;
                    const int_kind = bk.varint.encode(unsigned_int, &buffer, config.endian);
                    const encoded_len = int_kind.fullEncodedLen();
                    std.debug.assert(byte_limit >= encoded_len);
                    try writer.writeAll(buffer[0..encoded_len]);
                    return .{
                        .value_count = 1,
                        .byte_count = encoded_len,
                    };
                } else {
                    var byte_count: usize = 0;
                    for (values) |value| {
                        const unsigned_int = bk.varint.zigzag.anyToUnsigned(Int, value);
                        var buffer: [bk.varint.IntKind.fullEncodedLen(.maximum)]u8 = undefined;
                        const int_kind = bk.varint.encode(unsigned_int, &buffer, config.endian);
                        const encoded_len = int_kind.fullEncodedLen();
                        try writer.writeAll(buffer[0..encoded_len]);
                        byte_count += encoded_len;
                    }
                    return .{
                        .value_count = values.len,
                        .byte_count = byte_count,
                    };
                }
            }

            pub const encode_min_size: usize = @max(
                bk.varint.IntKind.fullEncodedLen(.fromValue(std.math.maxInt(V))),
                bk.varint.IntKind.fullEncodedLen(.fromValue(bk.varint.zigzag.anyToUnsigned(V, std.math.maxInt(V)))),
                bk.varint.IntKind.fullEncodedLen(.fromValue(bk.varint.zigzag.anyToUnsigned(V, std.math.minInt(V)))),
            );

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                values: []V,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) bk.DecodeFromReaderError!void {
                try decodeImpl(reader, config, false, values, decoded_count, maybe_diag);
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                config: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) bk.DecodeSkipError!void {
                try decodeImpl(reader, config, true, value_count, decoded_count, maybe_diag);
            }

            fn decodeImpl(
                reader: *std.Io.Reader,
                config: bk.Config,
                comptime skip: bool,
                values_or_count: if (skip) usize else []V,
                decoded_count: *usize,
                maybe_diag: ?*IntDecodeDiag,
            ) !void {
                const value_count: usize = if (skip) values_or_count else values_or_count.len;
                const values = if (skip) blk: {
                    var void_slice: []void = &.{};
                    void_slice.len = value_count;
                    break :blk void_slice;
                } else values_or_count;

                decoded_count.* = value_count;
                for (values, 0..value_count) |*value, index| {
                    errdefer decoded_count.* = index;

                    const raw_int = try bk.varint.decodeReader(reader, config.endian);
                    switch (signedness) {
                        .unsigned => {
                            if (raw_int > std.math.maxInt(V)) {
                                if (maybe_diag) |diag| diag.raw_int = raw_int;
                                return error.DecodeFailed;
                            }
                            if (!skip) value.* = @intCast(raw_int);
                        },
                        .signed => {
                            const EncodedInt = bk.varint.zigzag.SignedAsUnsigned(Int);
                            if (raw_int > std.math.maxInt(EncodedInt)) {
                                if (maybe_diag) |diag| diag.raw_int = bk.varint.zigzag.signedFromUnsigned(i256, raw_int);
                                return error.DecodeFailed;
                            }
                            const encoded_int_unsigned: EncodedInt = @intCast(raw_int);
                            const decoded_int: Int = bk.varint.zigzag.signedFromUnsigned(Int, encoded_int_unsigned);
                            if (std.math.minInt(V) > decoded_int or decoded_int > std.math.maxInt(V)) {
                                if (maybe_diag) |diag| diag.raw_int = decoded_int;
                                return error.DecodeFailed;
                            }
                            if (!skip) value.* = @intCast(decoded_int);
                        },
                    }
                }
            }

            pub const free = null;
        }));

        /// Standard codec for a float.
        /// Never fails to encode or decode.
        /// Decode's initial state is write-only.
        pub const float: StdCodecSelf = .from(.implement(void, void, struct {
            const AsInt = std.meta.Int(.unsigned, @bitSizeOf(V));
            const as_int_codec: bk.Codec(AsInt) = .standard(.fixint);
            comptime {
                switch (V) {
                    f32, f64 => {},
                    else => @compileError("float codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                values: []const V,
                progress_stack: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                return try as_int_codec.encodeManyPartialRaw(
                    writer,
                    config,
                    @ptrCast(values),
                    progress_stack,
                    limit,
                    {},
                );
            }

            pub const encode_min_size: usize = @sizeOf(V);

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                values: []V,
                decoded_count: *usize,
                _: void,
            ) bk.DecodeFromReaderError!void {
                try reader.readSliceEndian(AsInt, @ptrCast(values), config.endian);
                decoded_count.* = values.len;
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                _: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                _: void,
            ) bk.DecodeSkipError!void {
                try reader.discardAll(@sizeOf(AsInt) * value_count);
                decoded_count.* = value_count;
            }

            pub const free = null;
        }));

        /// Standard codec for a UTF-8 codepoint.
        /// Failure to encode indicates an invalid codepoint value.
        /// Failure to decode indicates an invalid codepoint value.
        /// Decode's initial state is write-only.
        pub const utf8_codepoint: StdCodecSelf = .from(.implement(void, void, struct {
            comptime {
                switch (V) {
                    u1, u2, u3, u4, u5, u6, u7 => {},
                    u8, u16, u21, u32 => {},
                    else => @compileError("char codec is not implemented for " ++ @typeName(V)),
                }
            }

            fn codepointToBytes(buf: *[4]u8, value: V) ![]u8 {
                if (value > std.math.maxInt(u21)) {
                    return error.EncodeFailed;
                }
                const cp_val: u21 = @intCast(value);
                const cp_len = std.unicode.utf8CodepointSequenceLength(cp_val) catch
                    return error.EncodeFailed;
                const encoded = buf[0..cp_len];
                const actual_cp_len = std.unicode.utf8Encode(cp_val, encoded) catch
                    return error.EncodeFailed;
                std.debug.assert(cp_len == actual_cp_len);
                return encoded;
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                values: []const V,
                _: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                switch (V) {
                    u1, u2, u3, u4, u5, u6, u7 => |ByteSized| {
                        comptime if (@sizeOf(ByteSized) != @sizeOf(u8)) unreachable;
                        return byte.codec.encodeManyPartialRaw(writer, config, @ptrCast(values), null, limit, {});
                    },
                    u8, u16, u21, u32 => {
                        if (limit.toInt()) |byte_limit| {
                            var encoded_buf: [4]u8 = undefined;
                            const encoded = try codepointToBytes(&encoded_buf, values[0]);
                            std.debug.assert(byte_limit >= encoded.len);
                            try writer.writeAll(encoded);
                            return .{
                                .value_count = 1,
                                .byte_count = encoded.len,
                            };
                        } else {
                            var byte_count: usize = 0;
                            const start_index = if (V != u8) 0 else blk: {
                                const first_non_ascii_index = indexOfScalarCmpPos(V, values, 0, .gt, 127) orelse values.len;
                                try writer.writeAll(values[0..first_non_ascii_index]);
                                break :blk first_non_ascii_index;
                            };
                            for (values[start_index..]) |value| {
                                var encoded_buf: [4]u8 = undefined;
                                const encoded = try codepointToBytes(&encoded_buf, value);
                                try writer.writeAll(encoded);
                                byte_count += encoded.len;
                            }
                            return .{
                                .value_count = values.len,
                                .byte_count = byte_count,
                            };
                        }
                    },
                    else => comptime unreachable,
                }
            }

            pub const encode_min_size: usize = 4;

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: bk.Config,
                _: ?std.mem.Allocator,
                values: []V,
                decoded_count: *usize,
                _: void,
            ) bk.DecodeFromReaderError!void {
                try decodeImpl(reader, false, values, decoded_count);
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                _: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                _: void,
            ) bk.DecodeSkipError!void {
                try decodeImpl(reader, true, value_count, decoded_count);
            }

            fn decodeImpl(
                reader: *std.Io.Reader,
                comptime skip: bool,
                values_or_count: if (skip) usize else []V,
                decoded_count: *usize,
            ) !void {
                const value_count: usize = if (skip) values_or_count else values_or_count.len;
                const values = if (skip) blk: {
                    var void_slice: []void = &.{};
                    void_slice.len = value_count;
                    break :blk void_slice;
                } else values_or_count;

                decoded_count.* = value_count;
                for (values, 0..value_count) |*value, i| {
                    errdefer decoded_count.* = i;

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
                    if (!skip) value.* = @intCast(cp);
                }
            }

            pub const free = null;
        }));

        pub fn OptionalDecodeCtx(comptime PayloadCtx: type) type {
            return struct {
                diag: ?*BoolDecodeDiag,
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
        ///
        /// Also see:
        /// * `optionalNonStd`
        /// * `OptionalDecodeCtx`
        pub fn optional(payload: StdCodec(Child)) StdCodecSelf {
            return .optionalNonStd(.standard(payload));
        }

        /// Same as `optional`, but directly accepting a non-standard `payload` codec.
        /// Facilitates composition with non-standard codecs.
        pub fn optionalNonStd(payload: bk.Codec(Child)) StdCodecSelf {
            const EncodeCtx = payload.EncodeCtx;
            const DecodeCtx = OptionalDecodeCtx(payload.DecodeCtx);

            const decode_ctx_opt = switch (@typeInfo(payload.DecodeCtx)) {
                .void, .optional => true,
                else => false,
            };
            const DecodeCtxParam = if (decode_ctx_opt) ?DecodeCtx else DecodeCtx;

            const free_defined = payload.freeFn != null;
            const decode_init_defined = payload.decodeInitFn != null;

            const erased = Base.ImplementMethods(EncodeCtx, DecodeCtxParam, struct {
                const Unwrapped = @typeInfo(V).optional.child;

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    var bool_flag_dummy: u64 = 0;
                    const bool_flag: *u64, //
                    const payload_stack: ?*[encode_stack_size - 1]u64 //
                    = if (progress_stack) |ps| .{ &ps[0], ps[1..] } else .{ &bool_flag_dummy, null };

                    const value = &values[0];

                    var byte_count: usize = 0;
                    if (bool_flag.* == 0) {
                        bool_flag.* = 1;

                        const not_null = value.* != null;
                        const bool_counts = boolean.codec.encodeOnePartialRaw(
                            writer,
                            config,
                            &not_null,
                            null,
                            limit,
                            ctx,
                        ) catch |err| switch (err) {
                            error.WriteFailed => |e| return e,
                            error.EncodeFailed => unreachable, // bool never fails to encode
                        };
                        std.debug.assert(bool_counts.value_count == 1);
                        std.debug.assert(bool_counts.byte_count == 1);
                        byte_count += 1;
                    } else std.debug.assert(bool_flag.* == 1);

                    const remaining_limit = limit.subtract(byte_count).?;

                    const done: bool = if (value.*) |*payload_ptr| blk: {
                        if (remaining_limit.toInt()) |byte_limit| {
                            if (byte_limit < payload.encode_min_size) break :blk false;
                        }

                        const payload_counts = try payload.encodeOnePartialRaw(
                            writer,
                            config,
                            payload_ptr,
                            payload_stack,
                            remaining_limit,
                            {},
                        );
                        byte_count += payload_counts.byte_count;
                        break :blk switch (payload_counts.value_count) {
                            0 => false,
                            1 => true,
                            else => unreachable,
                        };
                    } else true;
                    if (done) bool_flag.* = 0; // reset

                    return .{
                        .value_count = if (done) 1 else 0,
                        .byte_count = byte_count,
                    };
                }

                pub const encode_min_size: usize = @max(
                    boolean.codec.encode_min_size,
                    payload.encode_min_size,
                );

                pub const encode_stack_size: usize =
                    1 + // used as a boolean value which is 0 or 1 to track whether the null bool was written
                    payload.encode_stack_size;

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
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeFromReaderError!void {
                    try decodeImpl(reader, config, false, gpa_opt, values, decoded_count, maybe_ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeSkipError!void {
                    try decodeImpl(reader, config, true, null, value_count, decoded_count, maybe_ctx);
                }

                fn decodeImpl(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    comptime skip: bool,
                    gpa_opt: ?if (skip) noreturn else std.mem.Allocator,
                    values_or_count: if (skip) usize else []V,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) !void {
                    const value_count: usize = if (skip) values_or_count else values_or_count.len;
                    const values = if (skip) blk: {
                        var void_slice: []void = &.{};
                        void_slice.len = value_count;
                        break :blk void_slice;
                    } else values_or_count;

                    const ctx: DecodeCtx = ctx: {
                        if (!decode_ctx_opt) break :ctx maybe_ctx;
                        break :ctx maybe_ctx orelse .{
                            .diag = null,
                            .pl = if (payload.DecodeCtx != void) null,
                        };
                    };

                    decoded_count.* = value_count;
                    for (values, 0..value_count) |*value, i| {
                        errdefer decoded_count.* = i;

                        const is_some = boolean.codec.decode(reader, null, config, ctx.diag) catch |err| switch (err) {
                            error.OutOfMemory => unreachable,
                            else => |e| return e,
                        };
                        if (!skip) {
                            if (is_some) {
                                if (!decode_init_defined or value.* == null) {
                                    value.* = @as(Unwrapped, undefined);
                                    try payload.decodeInitOne(gpa_opt, &value.*.?, ctx.pl);
                                }
                                try payload.decodeIntoOne(reader, gpa_opt, config, &value.*.?, ctx.pl);
                            } else {
                                if (decode_init_defined) if (value.*) |*pl| {
                                    payload.free(gpa_opt, pl, ctx.pl);
                                };
                                value.* = null;
                            }
                        } else {
                            if (is_some) {
                                try payload.decodeSkip(reader, config, 1, ctx.pl);
                            }
                        }
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    values: []const V,
                    maybe_ctx: DecodeCtxParam,
                ) void {
                    comptime if (!free_defined) unreachable;
                    const ctx: DecodeCtx = ctx: {
                        if (!decode_ctx_opt) break :ctx maybe_ctx;
                        break :ctx maybe_ctx orelse .{
                            .diag = null,
                            .pl = if (payload.DecodeCtx != void) null,
                        };
                    };
                    for (values) |*value| {
                        const unwrapped = if (value.*) |*unwrapped| unwrapped else continue;
                        payload.free(gpa_opt, unwrapped, ctx.pl);
                    }
                }
            });

            return .from(.{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,
                .encode_min_size = erased.encode_min_size,
                .encode_stack_size = erased.encode_stack_size,

                .DecodeCtx = DecodeCtxParam,
                .decodeInitFn = if (decode_init_defined) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .decodeSkipFn = erased.decodeSkip,
                .freeFn = if (free_defined) erased.free else null,
            });
        }

        const PackedBackingInt: type = switch (@typeInfo(V)) {
            .@"union" => std.meta.Int(.unsigned, @bitSizeOf(V)),
            .@"struct" => |s_info| switch (s_info.layout) {
                .@"packed" => s_info.backing_integer.?,
                else => @compileError(@typeName(V) ++ " is not a packed type."),
            },
            else => @compileError(@typeName(V) ++ " is not a packed type."),
        };

        pub fn packedFields(backing_int: StdCodec(PackedBackingInt)) StdCodecSelf {
            const EncodeCtx = backing_int.codec.EncodeCtx;
            const DecodeCtx = backing_int.codec.DecodeCtx;
            return .from(.implement(EncodeCtx, DecodeCtx, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    encode_ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    return backing_int.codec.encodeManyPartialRaw(
                        writer,
                        config,
                        @ptrCast(values),
                        progress_stack,
                        limit,
                        encode_ctx,
                    );
                }

                pub const encode_min_size: usize = backing_int.codec.encode_min_size;

                pub const encode_stack_size: usize = backing_int.codec.encode_stack_size;

                pub const decodeInit = null;

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    maybe_diag: DecodeCtx,
                ) bk.DecodeFromReaderError!void {
                    try backing_int.codec.decodeIntoManyRaw(
                        reader,
                        gpa_opt,
                        config,
                        @ptrCast(values),
                        decoded_count,
                        maybe_diag,
                    );
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    maybe_diag: DecodeCtx,
                ) bk.DecodeSkipError!void {
                    try backing_int.codec.decodeSkipManyRaw(
                        reader,
                        config,
                        value_count,
                        decoded_count,
                        maybe_diag,
                    );
                }

                pub const free = null;
            }));
        }

        pub fn TupleEncodeCtx(field_codecs: Fields) type {
            const EncodeCtx, _, _, _, _ = FieldContexts(field_codecs);
            return EncodeCtx;
        }

        pub fn TupleDecodeCtx(field_codecs: Fields) type {
            _, const DecodeCtx, _, _, _ = FieldContexts(field_codecs);
            return DecodeCtx;
        }

        /// Standard codec for a tuple, or a struct with named fields (no difference in encoding).
        /// Allocation requirement defined by whether any codec in field codecs requires allocation.
        /// Failure to encode and decode defined by all of the field codecs in sequence.
        /// Decode's initial state is defined for each field based on the respective codec.
        ///
        /// Also see:
        /// * `TupleEncodeCtx`.
        /// * `TupleDecodeCtx`.
        pub fn tuple(field_codecs: Fields) StdCodecSelf {
            const s_fields = @typeInfo(V).@"struct".fields;
            const EncodeCtx, //
            const DecodeCtx, //
            const decode_init_req, //
            const free_req, //
            const max_encode_min_size, //
            const max_encode_stack_size //
            = FieldContexts(field_codecs);

            const any_decode_init = decode_init_req == .need_decode_init;
            const any_free = free_req == .need_free;

            const erased = Base.ImplementMethods(EncodeCtx, DecodeCtx, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    var field_index_dummy: u64 = 0;
                    const field_index: *u64, //
                    const field_stack: ?*[encode_stack_size - 1]u64 //
                    = if (progress_stack) |ps| .{ &ps[0], ps[1..] } else .{ &field_index_dummy, null };
                    std.debug.assert(field_index.* <= s_fields.len);

                    const value = &values[0];

                    var byte_count: usize = 0;
                    inline for (s_fields, 0..) |s_field, i| if (field_index.* == i) {
                        const field: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                        const field_ctx = getFieldCtx(ctx, s_field.name, field.codec.EncodeCtx);
                        const field_ptr = &@field(value, s_field.name);

                        const remaining_limit = limit.subtract(byte_count).?;
                        if (remaining_limit.toInt()) |byte_limit| {
                            if (byte_limit < field.codec.encode_min_size) return .{
                                .value_count = 0,
                                .byte_count = byte_count,
                            };
                        }

                        const field_counts = try field.codec.encodeOnePartialRaw(
                            writer,
                            config,
                            field_ptr,
                            if (field_stack) |fs| fs[0..field.codec.encode_stack_size] else null,
                            remaining_limit,
                            field_ctx,
                        );
                        byte_count += field_counts.byte_count;
                        switch (field_counts.value_count) {
                            0 => return .{
                                .value_count = 0,
                                .byte_count = byte_count,
                            },
                            1 => field_index.* += 1,
                            else => unreachable,
                        }
                    };
                    field_index.* = 0; // reset
                    return .{
                        .value_count = 1,
                        .byte_count = byte_count,
                    };
                }

                pub const encode_min_size: usize = max_encode_min_size;

                pub const encode_stack_size: usize =
                    1 + // current field index
                    max_encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    comptime if (!any_decode_init) unreachable;
                    for (values, 0..) |*value, value_i| {
                        errdefer for (values[0..value_i]) |*prev| {
                            freeFieldSubset(s_fields.len, gpa_opt, prev, ctx);
                        };

                        inline for (s_fields, 0..) |s_field, s_field_i| {
                            errdefer freeFieldSubset(s_field_i, gpa_opt, value, ctx);
                            const field: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                            const field_ctx = getFieldCtx(ctx, s_field.name, field.codec.DecodeCtx);
                            const field_ptr = &@field(value, s_field.name);
                            try field.codec.decodeInitOne(gpa_opt, field_ptr, field_ctx);
                        }
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtx,
                ) bk.DecodeFromReaderError!void {
                    try decodeImpl(reader, config, false, gpa_opt, values, decoded_count, maybe_ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtx,
                ) bk.DecodeSkipError!void {
                    try decodeImpl(reader, config, true, null, value_count, decoded_count, maybe_ctx);
                }

                fn decodeImpl(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    comptime skip: bool,
                    gpa_opt: ?if (skip) noreturn else std.mem.Allocator,
                    values_or_count: if (skip) usize else []V,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtx,
                ) !void {
                    const value_count: usize = if (skip) values_or_count else values_or_count.len;
                    const values = if (skip) blk: {
                        var void_slice: []void = &.{};
                        void_slice.len = value_count;
                        break :blk void_slice;
                    } else values_or_count;

                    decoded_count.* = value_count;
                    for (values, 0..) |*value, i| {
                        errdefer decoded_count.* = i;

                        inline for (s_fields, 0..) |s_field, s_i| {
                            const field: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                            const field_ctx = getFieldCtx(maybe_ctx, s_field.name, field.codec.DecodeCtx);
                            if (!skip) {
                                errdefer freeFieldSubset(s_i, gpa_opt, value, maybe_ctx);
                                const field_ptr = &@field(value, s_field.name);
                                try field.codec.decodeIntoOne(reader, gpa_opt, config, field_ptr, field_ctx);
                            } else {
                                try field.codec.decodeSkip(reader, config, 1, field_ctx);
                            }
                        }
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    values: []const V,
                    ctx: DecodeCtx,
                ) void {
                    comptime if (!any_free) unreachable;
                    for (values) |*value| {
                        freeFieldSubset(s_fields.len, gpa_opt, value, ctx);
                    }
                }

                fn freeFieldSubset(
                    comptime n_fields_to_deinit: usize,
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtx,
                ) void {
                    inline for (s_fields[0..n_fields_to_deinit]) |s_field| {
                        const field: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                        const field_ctx = getFieldCtx(ctx, s_field.name, field.codec.DecodeCtx);
                        const field_ptr = &@field(value, s_field.name);
                        field.codec.free(gpa_opt, field_ptr, field_ctx);
                    }
                }

                fn getFieldCtx(
                    maybe_ctx: anytype,
                    comptime field_name: []const u8,
                    comptime FieldCtxType: type,
                ) FieldCtxType {
                    const CtxType = @TypeOf(maybe_ctx);
                    if (CtxType != EncodeCtx and CtxType != DecodeCtx) unreachable;

                    if (FieldCtxType == void) return {};
                    const ctx = switch (@typeInfo(CtxType)) {
                        .void => return {},
                        .optional => maybe_ctx orelse return null,
                        else => maybe_ctx,
                    };
                    return @field(ctx, field_name);
                }
            });

            return .from(.{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,
                .encode_min_size = erased.encode_min_size,
                .encode_stack_size = erased.encode_stack_size,

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = if (any_decode_init) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .decodeSkipFn = erased.decodeSkip,
                .freeFn = if (any_free) erased.free else null,
            });
        }

        pub fn TaggedUnionDecodeCtx(
            payload_codecs: Fields,
        ) type {
            _, const PayloadDecodeCtx, _, _, _ = FieldContexts(payload_codecs);
            return TaggedUnionDecodeCtxGeneric(PayloadDecodeCtx);
        }

        pub fn TaggedUnionDecodeCtxGeneric(comptime PayloadDecodeCtx: type) type {
            const Tag = @typeInfo(V).@"union".tag_type.?;
            return struct {
                diag: ?*StdCodec(Tag).DiscriminantDecodeCtx,
                pl: PayloadDecodeCtx,
            };
        }

        /// Standard codec for a tagged union, aka "enums" in the bincode specification, written in the context of rust.
        /// Allocation requirement defined by whether any codec in payload codecs requires allocation.
        /// Never fails to encode the discriminant, payload fallability is defined by `payload_codecs`.
        /// Failure to decode indicates either a failure to decode discriminant, or the potential payload.
        /// Decode's initial state is write-only, unless `decode_init_tag_opt` is specified; see that parameter's
        /// doc comment. Whether the payload's initial state is write-only or not depends on the payload
        /// codec of the specified tag.
        ///
        /// Also see:
        /// * `discriminant`.
        /// * `TaggedUnionEncodeCtx`.
        /// * `TaggedUnionDecodeCtx`.
        pub fn taggedUnion(
            /// If non-null, specifies the tag that `decodeInit` should initialize a value
            /// to, permitting `decode` to assume the `value` pointer is valid and initialized,
            /// and can be decoded into in-place, with the semantics of doing so for each variant
            /// being defined by the respective codec in `payload_codecs`.
            ///
            /// If null, decode's initial state is write-only, since it cannot be assumed
            /// that the union is properly initialized.
            comptime decode_init_tag_opt: ?@typeInfo(V).@"union".tag_type.?,
            payload_codecs: Fields,
        ) StdCodecSelf {
            const union_info = @typeInfo(V).@"union";
            const Tag = union_info.tag_type.?;

            const EncodeCtx, //
            const PayloadDecodeCtx, //
            _, //
            const free_req, //
            const max_encode_min_size, //
            const max_encode_stack_size //
            = FieldContexts(payload_codecs);
            const DecodeCtx = TaggedUnionDecodeCtxGeneric(PayloadDecodeCtx);

            const pl_field_kind: bk.std_reflect.FieldGroupKind = .fromType(@FieldType(DecodeCtx, "pl"));
            const any_free = free_req == .need_free;

            const DecodeCtxParam = switch (pl_field_kind) {
                .all_void, .all_opt_or_void => ?DecodeCtx,
                .some_required => DecodeCtx,
            };

            const erased = Base.ImplementMethods(EncodeCtx, DecodeCtxParam, struct {
                const TaggedUnionImpl = @This();
                const tag_codec: bk.Codec(Tag) = .standard(.discriminant);

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    maybe_ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    var tag_flag_dummy: u64 = 0;
                    const tag_flag: *u64, //
                    const payload_stack: ?*[encode_stack_size - 1]u64 //
                    = if (progress_stack) |ps| .{ &ps[0], ps[1..] } else .{ &tag_flag_dummy, null };

                    const value = &values[0];

                    var byte_count: usize = 0;
                    if (tag_flag.* == 0) {
                        tag_flag.* = 1;

                        const current_tag: union_info.tag_type.? = value.*;
                        const tag_counts = tag_codec.encodeOnePartialRaw(
                            writer,
                            config,
                            &current_tag,
                            null,
                            limit,
                            {},
                        ) catch |err| switch (err) {
                            error.WriteFailed => |e| return e,
                            error.EncodeFailed => unreachable, // tag never fails to encode
                        };
                        std.debug.assert(tag_counts.value_count == 1);
                        byte_count += tag_counts.byte_count;
                    } else std.debug.assert(tag_flag.* == 1);

                    const remaining_limit = limit.subtract(byte_count).?;

                    const payload_counts: bk.EncodedCounts = switch (value.*) {
                        inline else => |*payload_ptr, itag| pl_counts: {
                            const Payload = @TypeOf(payload_ptr.*);
                            const payload_codec: bk.Codec(Payload) = @field(payload_codecs, @tagName(itag)).codec;
                            const payload_ctx: payload_codec.EncodeCtx = ctx: {
                                const ctx = switch (@typeInfo(payload_codec.EncodeCtx)) {
                                    .void => break :ctx {},
                                    .optional => maybe_ctx orelse break :ctx null,
                                    else => maybe_ctx,
                                };
                                break :ctx @field(ctx, @tagName(itag));
                            };

                            if (remaining_limit.toInt()) |byte_limit| {
                                if (byte_limit < payload_codec.encode_min_size) return .{
                                    .value_count = 0,
                                    .byte_count = byte_count,
                                };
                            }

                            break :pl_counts try payload_codec.encodeOnePartialRaw(
                                writer,
                                config,
                                payload_ptr,
                                if (payload_stack) |ps| ps[0..payload_codec.encode_stack_size] else null,
                                remaining_limit,
                                payload_ctx,
                            );
                        },
                    };

                    byte_count += payload_counts.byte_count;
                    switch (payload_counts.value_count) {
                        0 => return .{
                            .value_count = 0,
                            .byte_count = byte_count,
                        },
                        1 => tag_flag.* = 0, // reset
                        else => unreachable,
                    }

                    return .{
                        .value_count = 1,
                        .byte_count = byte_count,
                    };
                }

                pub const encode_min_size: usize = @max(
                    tag_codec.encode_min_size,
                    max_encode_min_size,
                );

                pub const encode_stack_size: usize =
                    1 + // used as a boolean value which is 0 or 1 to track whether the tag was written
                    max_encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    maybe_ctx: DecodeCtxParam,
                ) std.mem.Allocator.Error!void {
                    const decode_init_tag = comptime decode_init_tag_opt.?;
                    const ctx: DecodeCtx = unwrapMaybeCtx(maybe_ctx);

                    const Payload = @FieldType(V, @tagName(decode_init_tag));
                    const payload_codec: StdCodec(Payload) = @field(payload_codecs, @tagName(decode_init_tag));
                    const payload_ctx: payload_codec.DecodeCtx = getPlCtx(ctx, @tagName(decode_init_tag), payload_codec.DecodeCtx);

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
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeFromReaderError!void {
                    try decodeImpl(reader, config, false, gpa_opt, values, decoded_count, maybe_ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeSkipError!void {
                    try decodeImpl(reader, config, true, null, value_count, decoded_count, maybe_ctx);
                }

                fn decodeImpl(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    comptime skip: bool,
                    gpa_opt: ?if (skip) noreturn else std.mem.Allocator,
                    values_or_count: if (skip) usize else []V,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) !void {
                    const value_count: usize = if (skip) values_or_count else values_or_count.len;
                    const values = if (skip) blk: {
                        var void_slice: []void = &.{};
                        void_slice.len = value_count;
                        break :blk void_slice;
                    } else values_or_count;

                    const valid_init_state = comptime decode_init_tag_opt != null;
                    const ctx: DecodeCtx = unwrapMaybeCtx(maybe_ctx);

                    decoded_count.* = values.len;
                    for (values, 0..value_count) |*value, i| {
                        errdefer decoded_count.* = i;

                        const tag = tag_codec.decode(reader, null, config, ctx.diag) catch |err| switch (err) {
                            error.OutOfMemory => unreachable,
                            else => |e| return e,
                        };
                        switch (tag) {
                            inline else => |decoded_tag| {
                                const Payload = @FieldType(V, @tagName(decoded_tag));
                                const payload: StdCodec(Payload) = @field(payload_codecs, @tagName(decoded_tag));
                                const payload_ctx: payload.codec.DecodeCtx = getPlCtx(ctx, @tagName(decoded_tag), payload.codec.DecodeCtx);

                                if (!skip) {
                                    // if there's no valid inital state to worry about, just ovewrite and decode
                                    if (!valid_init_state) {
                                        value.* = @unionInit(V, @tagName(decoded_tag), undefined);
                                        const payload_ptr = &@field(value, @tagName(decoded_tag));
                                        try payload.codec.decodeInitOne(gpa_opt, payload_ptr, payload_ctx);

                                        // if there's a valid initial state and it matches the decoded tag, decode the payload in-place.
                                    } else if (value.* != decoded_tag) {
                                        // otherwise, initialize the new payload, free the old one, set the new payload, and then decode into it.
                                        var payload_val: @FieldType(V, @tagName(decoded_tag)) = undefined;
                                        try payload.codec.decodeInitOne(gpa_opt, &payload_val, payload_ctx);
                                        if (any_free) TaggedUnionImpl.free(gpa_opt, value[0..1], ctx);
                                        value.* = @unionInit(V, @tagName(decoded_tag), payload_val);
                                    }

                                    const payload_ptr = &@field(value, @tagName(decoded_tag));
                                    try payload.codec.decodeIntoOne(reader, gpa_opt, config, payload_ptr, payload_ctx);
                                } else {
                                    try payload.codec.decodeSkip(reader, config, 1, payload_ctx);
                                }
                            },
                        }
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    values: []const V,
                    maybe_ctx: DecodeCtxParam,
                ) void {
                    comptime if (!any_free) unreachable;
                    const ctx: DecodeCtx = unwrapMaybeCtx(maybe_ctx);
                    for (values) |*value| switch (value.*) {
                        inline else => |*payload_ptr, itag| {
                            const Payload = @FieldType(V, @tagName(itag));
                            const payload: StdCodec(Payload) = @field(payload_codecs, @tagName(itag));
                            const payload_ctx: payload.codec.DecodeCtx = getPlCtx(ctx, @tagName(itag), payload.codec.DecodeCtx);
                            payload.codec.free(gpa_opt, payload_ptr, payload_ctx);
                        },
                    };
                }

                fn unwrapMaybeCtx(maybe_ctx: DecodeCtxParam) DecodeCtx {
                    return switch (pl_field_kind) {
                        .all_void => maybe_ctx orelse .{
                            .diag = null,
                            .pl = {},
                        },
                        .all_opt_or_void => maybe_ctx orelse .{
                            .diag = null,
                            .pl = null,
                        },
                        .some_required => maybe_ctx,
                    };
                }

                fn getPlCtx(
                    maybe_ctx: anytype,
                    comptime field_name: []const u8,
                    comptime FieldCtxType: type,
                ) FieldCtxType {
                    const CtxType = @TypeOf(maybe_ctx);
                    if (CtxType != EncodeCtx and CtxType != DecodeCtx) unreachable;

                    if (FieldCtxType == void) return {};
                    const union_ctx = switch (@typeInfo(CtxType)) {
                        .void => return {},
                        .optional => maybe_ctx orelse return null,
                        else => maybe_ctx,
                    };
                    const pl_ctx = if (@typeInfo(FieldCtxType) == .optional)
                        union_ctx.pl orelse return null
                    else
                        union_ctx.pl;
                    return @field(pl_ctx, field_name);
                }
            });

            return .from(.{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,
                .encode_min_size = erased.encode_min_size,
                .encode_stack_size = erased.encode_stack_size,

                .DecodeCtx = DecodeCtxParam,
                .decodeInitFn = if (decode_init_tag_opt != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .decodeSkipFn = erased.decodeSkip,
                .freeFn = if (any_free) erased.free else null,
            });
        }

        pub const DiscriminantDecodeCtx = struct {
            /// Value of the actual decoded u32 with an erroneous value.
            /// Only set if when `error.DecodeFailed` is returned.
            real_int: ?u32,

            pub const init: DiscriminantDecodeCtx = .{ .real_int = null };
        };

        /// Standard codec for an enum used as a discriminant,
        /// aka the tag of a tagged union, aka the tag of a rust enum.
        /// Failure to decode indicates the value overflowed or didn't match a valid value.
        /// Decode's initial state is write-only.
        pub const discriminant: StdCodecSelf = .from(.implement(void, ?*DiscriminantDecodeCtx, struct {
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

            const u32_codec: bk.Codec(u32) = .standard(.int);

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                values: []const V,
                progress_stack: ?*[encode_stack_size]u64,
                limit: std.Io.Limit,
                _: void,
            ) bk.EncodeToWriterError!bk.EncodedCounts {
                if (@sizeOf(enum_info.tag_type) == @sizeOf(u32)) {
                    return try u32_codec.encodeManyPartialRaw(writer, config, @ptrCast(values), progress_stack, limit, {});
                } else {
                    const as_u32: u32 = @intFromEnum(values[0]);
                    return try u32_codec.encodeOnePartialRaw(writer, config, &as_u32, progress_stack, limit, {});
                }
            }

            pub const encode_min_size: usize = u32_codec.encode_min_size;

            pub const encode_stack_size: usize = 0;

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                values: []V,
                decoded_count: *usize,
                maybe_diag: ?*DiscriminantDecodeCtx,
            ) bk.DecodeFromReaderError!void {
                try decodeImpl(reader, config, false, values, decoded_count, maybe_diag);
            }

            pub fn decodeSkip(
                reader: *std.Io.Reader,
                config: bk.Config,
                value_count: usize,
                decoded_count: *usize,
                maybe_diag: ?*DiscriminantDecodeCtx,
            ) bk.DecodeSkipError!void {
                try decodeImpl(reader, config, true, value_count, decoded_count, maybe_diag);
            }

            fn decodeImpl(
                reader: *std.Io.Reader,
                config: bk.Config,
                comptime skip: bool,
                values_or_count: if (skip) usize else []V,
                decoded_count: *usize,
                maybe_diag: ?*DiscriminantDecodeCtx,
            ) !void {
                const value_count: usize = if (skip) values_or_count else values_or_count.len;
                const values = if (skip) blk: {
                    var void_slice: []void = &.{};
                    void_slice.len = value_count;
                    break :blk void_slice;
                } else values_or_count;

                decoded_count.* = values.len;
                for (values, 0..value_count) |*value, i| {
                    errdefer decoded_count.* = i;

                    const as_u32 = u32_codec.decode(reader, null, config, null) catch |err| switch (err) {
                        error.OutOfMemory => unreachable,
                        else => |e| return e,
                    };
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
                    if (!skip) value.* = std.enums.fromInt(V, raw) orelse {
                        if (maybe_diag) |diag| diag.real_int = as_u32;
                        return error.DecodeFailed;
                    };
                }
            }

            pub const free = null;
        }));

        /// Standard codec for an array.
        /// Allocation requirement defined by element codec.
        /// Decode's initial state is defined as an array of initial states conforming to `element_codec`'s expectations.
        ///
        /// Also see `byte_array`.
        pub fn array(element: StdCodec(Element)) StdCodecSelf {
            return .arrayNonStd(.standard(element));
        }

        /// Same as `array`, but directly accepting a non-standard `element` codec.
        /// Facilitates composition with non-standard codecs.
        pub fn arrayNonStd(element: bk.Codec(Element)) StdCodecSelf {
            const EncodeCtx = element.EncodeCtx;
            const DecodeCtx = element.DecodeCtx;

            const array_len = switch (@typeInfo(V)) {
                .array => |info| info.len,
                else => @compileError("array codec not is not implemented for type " ++ @typeName(V)),
            };

            const erased = Base.ImplementMethods(EncodeCtx, DecodeCtx, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    var elem_index_dummy: u64 = 0;
                    const elem_index: *u64, //
                    const elem_stack: ?*[encode_stack_size - 1]u64 //
                    = if (progress_stack) |ps| .{ &ps[0], ps[1..] } else .{ &elem_index_dummy, null };

                    const flattened: []const Element = @ptrCast(values); // flatten `[][n]E` as `[]E`.

                    const elems_counts = try element.encodeManyPartialRaw(
                        writer,
                        config,
                        flattened[elem_index.*..],
                        elem_stack,
                        limit,
                        ctx,
                    );
                    const array_count = (elem_index.* + elems_counts.value_count) / array_len;
                    elem_index.* = (elem_index.* + elems_counts.value_count) % array_len;

                    return .{
                        .value_count = array_count,
                        .byte_count = elems_counts.byte_count,
                    };
                }

                pub const encode_min_size: usize = element.encode_min_size;

                pub const encode_stack_size: usize =
                    1 + // current element index
                    element.encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: element.DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    try element.decodeInitMany(gpa_opt, @ptrCast(values), ctx); // flatten `[][n]E` as `[]E`.
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeFromReaderError!void {
                    defer {
                        // since we pass `decoded_count` directly into the flattened call,
                        // this is going to be `value_count * array_len`, so the actual
                        // number of arrays decoded is `decoded_count.* / array_len`.
                        decoded_count.* = @divExact(decoded_count.*, array_len);
                    }
                    try element.decodeIntoManyRaw(
                        reader,
                        gpa_opt,
                        config,
                        @ptrCast(values), // flatten `[][n]E` as `[]E`.
                        decoded_count,
                        ctx,
                    );
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeSkipError!void {
                    defer {
                        // since we pass `decoded_count` directly into the flattened call,
                        // this is going to be `value_count * array_len`, so the actual
                        // number of arrays decoded is `decoded_count.* / array_len`.
                        decoded_count.* = @divExact(decoded_count.*, array_len);
                    }
                    try element.decodeSkipManyRaw(
                        reader,
                        config,
                        value_count * array_len,
                        decoded_count,
                        ctx,
                    );
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    values: []const V,
                    ctx: DecodeCtx,
                ) void {
                    element.freeMany(gpa_opt, @ptrCast(values), ctx); // flatten `[]const [n]E` as `[]E`.
                }
            });

            return .from(.{
                .EncodeCtx = element.EncodeCtx,
                .encodeFn = erased.encode,
                .encode_min_size = erased.encode_min_size,
                .encode_stack_size = erased.encode_stack_size,

                .DecodeCtx = element.DecodeCtx,
                .decodeInitFn = if (element.decodeInitFn != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .decodeSkipFn = erased.decodeSkip,
                .freeFn = if (element.freeFn != null) erased.free else null,
            });
        }

        /// Standard codec for a single item pointer.
        /// Disallows `Child = [n]T` and `Child = @Vector(n, T)`, see `arrayPtr` instead.
        ///
        /// Also see `singleItemPtrNonStd`.
        pub fn singleItemPtr(child: StdCodec(Child)) StdCodecSelf {
            return .singleItemPtrNonStd(.standard(child));
        }

        /// Same as `singleItemPtr`, but directly accepting a non-standard `child` codec.
        /// Facilitates composition with non-standard codecs.
        pub fn singleItemPtrNonStd(child: bk.Codec(Child)) StdCodecSelf {
            const EncodeCtx = child.EncodeCtx;
            const DecodeCtx = child.DecodeCtx;
            return .from(.implement(EncodeCtx, DecodeCtx, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .one) @compileError(
                        "single item ptr codec is not implemented for type " ++ @typeName(V),
                    );
                    if (@typeInfo(ptr_info.child) == .array or
                        @typeInfo(ptr_info.child) == .vector //
                    ) @compileError(
                        "single item ptr codec should not be used for type " ++ @typeName(V) ++
                            ", see `arrayPtr` instead",
                    );
                }

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    return try child.encodeOnePartialRaw(
                        writer,
                        config,
                        values[0],
                        progress_stack,
                        limit,
                        ctx,
                    );
                }

                pub const encode_min_size: usize = child.encode_min_size;

                pub const encode_stack_size: usize = child.encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    const gpa = gpa_opt.?;
                    for (values, 0..) |*p_ptr, i| {
                        errdefer free(gpa, values[0..i], ctx);
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
                        try child.decodeInitOne(gpa, ptr, ctx);
                        p_ptr.* = ptr;
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeFromReaderError!void {
                    decoded_count.* = values.len;
                    for (values, 0..) |ptr, i| {
                        errdefer decoded_count.* = i;
                        try child.decodeIntoOne(reader, gpa_opt, config, @constCast(ptr), ctx);
                    }
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeSkipError!void {
                    try child.decodeSkipManyRaw(reader, config, value_count, decoded_count, ctx);
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    ptr_list: []const V,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    for (ptr_list) |ptr| {
                        child.free(gpa, ptr, ctx);
                        gpa.destroy(ptr);
                    }
                }
            }));
        }

        /// Standard codec for a slice. Encodes the length.
        /// Requires allocation, for the slice, and possibly for the elements (based on element codec).
        ///
        /// Also see:
        /// * `byte_array`.
        /// * `sliceNonStd`.
        pub fn slice(element: StdCodec(Element)) StdCodecSelf {
            return .sliceNonStd(.standard(element));
        }

        /// Same as `sliceNonStd`, but directly accepting a non-standard `element` codec.
        /// Facilitates composition with non-standard codecs.
        pub fn sliceNonStd(element: bk.Codec(Element)) StdCodecSelf {
            const EncodeCtx = element.EncodeCtx;
            const DecodeCtx = element.DecodeCtx;
            const erased = Base.ImplementMethods(EncodeCtx, DecodeCtx, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .slice) @compileError(
                        "single item ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    var len_flag_dummy: u64 = 0;
                    var elem_index_dummy: u64 = 0;
                    const len_flag: *u64, //
                    const elem_index: *u64, //
                    const elem_stack: ?*[encode_stack_size - 2]u64 //
                    = if (progress_stack) |ps|
                        .{ &ps[0], &ps[1], ps[2..] }
                    else
                        .{ &len_flag_dummy, &elem_index_dummy, null };

                    const value = values[0];

                    var byte_count: usize = 0;
                    if (len_flag.* == 0) {
                        len_flag.* = 1;
                        std.debug.assert(elem_index.* == 0);

                        const len_counts = length.codec.encodeOnePartialRaw(
                            writer,
                            config,
                            &value.len,
                            null,
                            limit,
                            {},
                        ) catch |err| switch (err) {
                            error.WriteFailed => |e| return e,
                            error.EncodeFailed => unreachable, // len never fails to encode
                        };
                        std.debug.assert(len_counts.value_count == 1);
                        byte_count += len_counts.byte_count;
                    } else std.debug.assert(len_flag.* == 1);

                    const remaining_limit = limit.subtract(byte_count).?;

                    if (remaining_limit.toInt()) |byte_limit| {
                        if (byte_limit < element.encode_min_size) return .{
                            .value_count = 0,
                            .byte_count = byte_count,
                        };
                    }

                    const elems_counts = try element.encodeManyPartialRaw(
                        writer,
                        config,
                        value[elem_index.*..],
                        elem_stack,
                        remaining_limit,
                        ctx,
                    );
                    byte_count += elems_counts.byte_count;
                    elem_index.* += elems_counts.value_count;
                    std.debug.assert(elem_index.* <= value.len);

                    const done = elem_index.* == value.len;
                    if (done) len_flag.*, elem_index.* = .{ 0, 0 }; // reset
                    return .{
                        .value_count = if (done) 1 else 0,
                        .byte_count = byte_count,
                    };
                }

                pub const encode_min_size: usize = @max(
                    length.codec.encode_min_size,
                    element.encode_min_size,
                );

                pub const encode_stack_size: usize =
                    1 + // used as a boolean value which is 0 or 1 to track whether the length was written
                    1 + // current element index
                    element.encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    _: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    _ = gpa_opt.?;
                    @memset(values, &.{});
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeFromReaderError!void {
                    try decodeImpl(reader, config, false, gpa_opt, values, decoded_count, ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeSkipError!void {
                    try decodeImpl(reader, config, true, null, value_count, decoded_count, ctx);
                }

                fn decodeImpl(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    comptime skip: bool,
                    gpa_opt: ?if (skip) noreturn else std.mem.Allocator,
                    values_or_count: if (skip) usize else []V,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) !void {
                    const gpa = if (!skip) gpa_opt.?;

                    const value_count: usize = if (skip) values_or_count else values_or_count.len;
                    const values = if (skip) blk: {
                        var void_slice: []void = &.{};
                        void_slice.len = value_count;
                        break :blk void_slice;
                    } else values_or_count;

                    decoded_count.* = value_count;
                    for (values, 0..) |*value, i| {
                        errdefer decoded_count.* = i;

                        const len = length.codec.decode(reader, null, config, null) catch |err| switch (err) {
                            error.OutOfMemory => unreachable,
                            else => |e| return e,
                        };
                        if (!skip) {
                            const value_init_len = value.len;
                            if (len != value_init_len) {
                                if (len < value_init_len) {
                                    element.freeMany(gpa, value.*[len..], ctx);
                                }

                                if (gpa.resize(@constCast(value.*), len)) {
                                    value.len = len;
                                } else if (gpa.remap(@constCast(value.*), len)) |new_slice| {
                                    value.* = new_slice;
                                } else {
                                    const new_slice = try gpa.alignedAlloc(
                                        Element,
                                        .fromByteUnits(ptr_info.alignment),
                                        len,
                                    );
                                    errdefer gpa.free(new_slice);

                                    const amt = @min(value_init_len, len);
                                    @memcpy(new_slice[0..amt], value.*[0..amt]);
                                    gpa.free(value.*);
                                    value.* = new_slice;
                                }

                                if (len > value_init_len) {
                                    element.decodeInitMany(gpa, @constCast(value.*[value_init_len..]), ctx) catch |err| {
                                        // free the slice and its initialized elements and set it to empty, so that
                                        // the errdefer above can safely free it along with every other slice value.
                                        element.freeMany(gpa, value.*[0..value_init_len], ctx);
                                        gpa.free(value.*);
                                        value.* = &.{};
                                        return err;
                                    };
                                }
                            }
                            try element.decodeIntoMany(reader, gpa, config, @constCast(value.*), ctx);
                        } else {
                            try element.decodeSkip(reader, config, len, ctx);
                        }
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    slice_list: []const V,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    for (slice_list) |slice_value| {
                        element.freeMany(gpa_opt, slice_value, ctx);
                        gpa.free(slice_value);
                    }
                }
            });

            return .from(.{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,
                .encode_min_size = erased.encode_min_size,
                .encode_stack_size = erased.encode_stack_size,

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = erased.decodeInit,
                .decodeFn = erased.decode,
                .decodeSkipFn = erased.decodeSkip,
                .freeFn = erased.free,
            });
        }

        /// Standard codec for an array pointer. Encodes the length.
        /// Also see `byte_array_ptr`.
        /// Decoding allocates the result.
        ///
        /// Also see `arrayPtrNonStd`.
        pub fn arrayPtr(element: StdCodec(Element)) StdCodecSelf {
            return .arrayPtrNonStd(.standard(element));
        }

        /// Standard codec for an array pointer. Encodes the length.
        /// Also see `byte_array_ptr`.
        pub fn arrayPtrNonStd(element: bk.Codec(Element)) StdCodecSelf {
            const EncodeCtx = element.EncodeCtx;
            const DecodeCtx = element.DecodeCtx;
            return .from(.implement(EncodeCtx, DecodeCtx, struct {
                const ptr_info = @typeInfo(V).pointer;
                const array_len = @typeInfo(ptr_info.child).array.len;
                comptime {
                    if (ptr_info.size != .one or @typeInfo(ptr_info.child) != .array) @compileError(
                        "array ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }
                const AsSlice = Pointer(
                    .slice,
                    .{
                        .@"const" = ptr_info.is_const,
                        .@"volatile" = ptr_info.is_volatile,
                        .@"allowzero" = ptr_info.is_allowzero,
                        .@"addrspace" = ptr_info.address_space,
                        .@"align" = ptr_info.alignment,
                    },
                    Element,
                    null,
                );

                const slice_codec: bk.Codec(AsSlice) = .standard(.sliceNonStd(element));
                const array_codec: bk.Codec(ptr_info.child) = .standard(.arrayNonStd(element));

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const V,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    const as_slice: AsSlice = values[0];
                    return try slice_codec.encodeOnePartialRaw(writer, config, &as_slice, progress_stack, limit, ctx);
                }

                pub const encode_min_size: usize = @max(
                    length.codec.encode_min_size,
                    array_codec.encode_min_size,
                );

                pub const encode_stack_size: usize = slice_codec.encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    const gpa = gpa_opt.?;

                    for (values, 0..) |*value, i| {
                        errdefer free(gpa, values[0..i], ctx);
                        const array_ptr = (try gpa.alignedAlloc(
                            @typeInfo(ptr_info.child).array.child,
                            .fromByteUnits(ptr_info.alignment),
                            array_len,
                        ))[0..array_len];
                        errdefer gpa.free(array_ptr);
                        value.* = array_ptr;
                        try array_codec.decodeInitOne(gpa, @constCast(value.*), ctx);
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeFromReaderError!void {
                    try decodeImpl(reader, config, false, gpa_opt, values, decoded_count, ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeSkipError!void {
                    try decodeImpl(reader, config, true, null, value_count, decoded_count, ctx);
                }

                fn decodeImpl(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    comptime skip: bool,
                    gpa_opt: ?if (skip) noreturn else std.mem.Allocator,
                    values_or_count: if (skip) usize else []V,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) !void {
                    const value_count: usize = if (skip) values_or_count else values_or_count.len;
                    const values = if (skip) blk: {
                        var void_slice: []void = &.{};
                        void_slice.len = value_count;
                        break :blk void_slice;
                    } else values_or_count;

                    decoded_count.* = values.len;
                    for (values, 0..) |*value, i| {
                        errdefer decoded_count.* = i;

                        const actual_len = length.codec.decode(reader, null, config, null) catch |err| switch (err) {
                            error.OutOfMemory => unreachable,
                            else => |e| return e,
                        };
                        if (actual_len != array_len) return error.DecodeFailed;

                        if (!skip) {
                            try array_codec.decodeIntoOne(reader, gpa_opt, config, @constCast(value.*), ctx);
                        } else {
                            try array_codec.decodeSkip(reader, config, 1, ctx);
                        }
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    array_ptr_list: []const V,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    for (array_ptr_list) |array_ptr_value| {
                        array_codec.free(gpa_opt, array_ptr_value, ctx);
                        gpa.free(array_ptr_value);
                    }
                }
            }));
        }

        const maybe_array_list_info: ?bk.std_reflect.ArrayListInfo = .from(V);
        pub const ArrayListElem: ?type = if (maybe_array_list_info) |al_info| al_info.Element else null;

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
        ///
        /// Also see `arrayListNonStd`.
        pub fn arrayList(
            element: StdCodec(ArrayListElem orelse void),
        ) StdCodecSelf {
            return .arrayListNonStd(.standard(element));
        }

        /// Same as `arrayList`, but directly accepting a non-standard `element` codec.
        /// Facilitates composition with non-standard codecs.
        pub fn arrayListNonStd(
            element: bk.Codec(ArrayListElem orelse void),
        ) StdCodecSelf {
            const ArrayList = std.array_list.Aligned(
                ArrayListElem.?,
                maybe_array_list_info.?.alignment,
            );

            const slice_codec: bk.Codec(ArrayList.Slice) = .standard(.sliceNonStd(element));

            const EncodeCtx = element.EncodeCtx;
            const DecodeCtx = element.DecodeCtx;
            return .from(.implement(EncodeCtx, DecodeCtx, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const ArrayList,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    ctx: EncodeCtx,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    return try slice_codec.encodeOnePartialRaw(
                        writer,
                        config,
                        &values[0].items,
                        progress_stack,
                        limit,
                        ctx,
                    );
                }

                pub const encode_min_size: usize = slice_codec.encode_min_size;

                pub const encode_stack_size: usize = slice_codec.encode_stack_size;

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []ArrayList,
                    _: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    _ = gpa_opt.?;
                    @memset(values, .empty);
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []ArrayList,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeFromReaderError!void {
                    try decodeImpl(reader, config, false, gpa_opt, values, decoded_count, ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) bk.DecodeSkipError!void {
                    try decodeImpl(reader, config, true, null, value_count, decoded_count, ctx);
                }

                fn decodeImpl(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    comptime skip: bool,
                    gpa_opt: ?if (skip) noreturn else std.mem.Allocator,
                    values_or_count: if (skip) usize else []V,
                    decoded_count: *usize,
                    ctx: DecodeCtx,
                ) !void {
                    const gpa = if (!skip) gpa_opt.?;

                    const value_count: usize = if (skip) values_or_count else values_or_count.len;
                    const values = if (skip) blk: {
                        var void_slice: []void = &.{};
                        void_slice.len = value_count;
                        break :blk void_slice;
                    } else values_or_count;

                    decoded_count.* = values.len;
                    for (values, 0..) |*value, i| {
                        errdefer decoded_count.* = i;

                        const len = length.codec.decode(reader, null, config, null) catch |err| switch (err) {
                            error.OutOfMemory => unreachable,
                            else => |e| return e,
                        };

                        if (!skip) {
                            try value.ensureTotalCapacityPrecise(gpa, len);
                            if (len > value.items.len) {
                                const additional = value.addManyAsSliceAssumeCapacity(len - value.items.len);
                                element.decodeInitMany(gpa, additional, ctx) catch |err| {
                                    value.shrinkRetainingCapacity(len - additional.len);
                                    return err;
                                };
                            } else if (len < value.items.len) {
                                element.freeMany(gpa, value.items[len..], ctx);
                                value.shrinkRetainingCapacity(len);
                            }
                            std.debug.assert(value.items.len == len);

                            try element.decodeIntoMany(reader, gpa, config, value.items, ctx);
                        } else {
                            try element.decodeSkip(reader, config, len, ctx);
                        }
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    values: []const ArrayList,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    for (values) |*value| {
                        element.freeMany(gpa, value.items, ctx);
                        var copy = value.*;
                        copy.deinit(gpa);
                    }
                }
            }));
        }

        const maybe_ahm_info: ?bk.std_reflect.ArrayHashMapInfo = .from(V);
        pub const ArrayHashMapKey = if (maybe_ahm_info) |hm_info| hm_info.K else @compileError(@typeName(V) ++ " is not a hash map");
        pub const ArrayHashMapVal = if (maybe_ahm_info) |hm_info| hm_info.V else @compileError(@typeName(V) ++ " is not a hash map");

        pub fn ArrayHashMapCtxs(
            key: bk.Codec(ArrayHashMapKey),
            val: bk.Codec(ArrayHashMapVal),
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
        ///
        /// Also see:
        /// * `ArrayHashMapCtxs`
        /// * `arrayHashMapNonStd`
        pub fn arrayHashMap(
            std_key: StdCodec(if (maybe_ahm_info) |hm_info| hm_info.K else void),
            std_val: StdCodec(if (maybe_ahm_info) |hm_info| hm_info.V else void),
        ) StdCodecSelf {
            return .arrayHashMapNonStd(.standard(std_key), .standard(std_val));
        }

        /// Same as `arrayHashMap`, but directly accepting non-standard `key` & `val` codecs.
        /// Facilitates composition with non-standard codecs.
        pub fn arrayHashMapNonStd(
            key: bk.Codec(if (maybe_ahm_info) |hm_info| hm_info.K else void),
            val: bk.Codec(if (maybe_ahm_info) |hm_info| hm_info.V else void),
        ) StdCodecSelf {
            const hm_info = comptime maybe_ahm_info orelse @compileError(@typeName(V) ++ " is not an array hash map.");
            const Map = std.ArrayHashMapUnmanaged(
                hm_info.K,
                hm_info.V,
                hm_info.Context,
                hm_info.store_hash,
            );
            const Ctxs = ArrayHashMapCtxs(key, val);
            const EncodeCtx = Ctxs.EncodeCtx;
            const DecodeCtx = Ctxs.DecodeCtx;

            const encode_ctx_kind: bk.std_reflect.FieldGroupKind = .max(
                .fromType(@FieldType(EncodeCtx, "key")),
                .fromType(@FieldType(EncodeCtx, "val")),
            );
            const EncodeCtxParam = switch (encode_ctx_kind) {
                .some_required => EncodeCtx,
                .all_opt_or_void => ?EncodeCtx,
                .all_void => void,
            };
            const decode_ctx_kind: bk.std_reflect.FieldGroupKind = .max(
                .fromType(@FieldType(DecodeCtx, "key")),
                .fromType(@FieldType(DecodeCtx, "val")),
            );
            const DecodeCtxParam = switch (decode_ctx_kind) {
                .some_required => DecodeCtx,
                .all_opt_or_void => ?DecodeCtx,
                .all_void => void,
            };

            const EntryTuple = struct { *const hm_info.K, *const hm_info.V };
            const entry_codec: bk.Codec(EntryTuple) = .standard(.tuple(.{
                .singleItemPtrNonStd(key),
                .singleItemPtrNonStd(val),
            }));

            return .from(.implement(EncodeCtxParam, DecodeCtxParam, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    values: []const Map,
                    progress_stack: ?*[encode_stack_size]u64,
                    limit: std.Io.Limit,
                    maybe_ctx: EncodeCtxParam,
                ) bk.EncodeToWriterError!bk.EncodedCounts {
                    var len_flag_dummy: u64 = 0;
                    var elem_index_dummy: u64 = 0;
                    const len_flag: *u64, //
                    const entry_index: *u64, //
                    const entry_stack: ?*[encode_stack_size - 2]u64 //
                    = if (progress_stack) |ps|
                        .{ &ps[0], &ps[1], ps[2..] }
                    else
                        .{ &len_flag_dummy, &elem_index_dummy, null };

                    const key_ctx, const val_ctx = unwrapKeyValCtxs(.encode, maybe_ctx);

                    const value = &values[0];

                    var byte_count: usize = 0;
                    if (len_flag.* == 0) {
                        len_flag.* = 1;
                        std.debug.assert(entry_index.* == 0);

                        const len_counts = length.codec.encodeOnePartialRaw(
                            writer,
                            config,
                            &value.count(),
                            null,
                            limit,
                            {},
                        ) catch |err| switch (err) {
                            error.WriteFailed => |e| return e,
                            error.EncodeFailed => unreachable, // len never fails to encode
                        };
                        std.debug.assert(len_counts.value_count == 1);
                        byte_count += len_counts.byte_count;
                    } else std.debug.assert(len_flag.* == 1);

                    for (
                        value.keys()[entry_index.*..],
                        value.values()[entry_index.*..],
                        entry_index.*..value.count(),
                    ) |*k, *v, i| {
                        const entry_tuple: EntryTuple = .{ k, v };

                        const remaining_limit = limit.subtract(byte_count).?;
                        if (remaining_limit.toInt()) |byte_limit| {
                            if (byte_limit < entry_codec.encode_min_size) {
                                entry_index.* = i;
                                return .{
                                    .value_count = 0,
                                    .byte_count = byte_count,
                                };
                            }
                        }

                        const entry_counts = try entry_codec.encodeOnePartialRaw(
                            writer,
                            config,
                            &entry_tuple,
                            entry_stack,
                            remaining_limit,
                            if (EncodeCtxParam != void) .{ key_ctx, val_ctx },
                        );
                        byte_count += entry_counts.byte_count;
                        switch (entry_counts.value_count) {
                            0 => {
                                entry_index.* = i;
                                return .{
                                    .value_count = 0,
                                    .byte_count = byte_count,
                                };
                            },
                            1 => {},
                            else => unreachable,
                        }
                    }

                    len_flag.* = 0; // reset
                    entry_index.* = 0; // reset

                    return .{
                        .value_count = 1,
                        .byte_count = byte_count,
                    };
                }

                pub const encode_min_size: usize = @max(
                    length.codec.encode_min_size,
                    key.encode_min_size,
                    val.encode_min_size,
                );

                pub const encode_stack_size: usize =
                    1 + // used as a boolean value which is 0 or 1 to track whether the length was written
                    1 + // current entry index
                    entry_codec.encode_stack_size;

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
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    values: []Map,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeFromReaderError!void {
                    try decodeImpl(reader, config, false, gpa_opt, values, decoded_count, maybe_ctx);
                }

                pub fn decodeSkip(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    value_count: usize,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeSkipError!void {
                    try decodeImpl(reader, config, true, null, value_count, decoded_count, maybe_ctx);
                }

                fn decodeImpl(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    comptime skip: bool,
                    gpa_opt: ?if (skip) noreturn else std.mem.Allocator,
                    values_or_count: if (skip) usize else []V,
                    decoded_count: *usize,
                    maybe_ctx: DecodeCtxParam,
                ) !void {
                    const gpa = if (!skip) gpa_opt.?;

                    const value_count: usize = if (skip) values_or_count else values_or_count.len;
                    const values = if (skip) blk: {
                        var void_slice: []void = &.{};
                        void_slice.len = value_count;
                        break :blk void_slice;
                    } else values_or_count;

                    const key_ctx, const val_ctx = unwrapKeyValCtxs(.decode, maybe_ctx);

                    decoded_count.* = values.len;
                    for (values, 0..) |*value, i| {
                        errdefer decoded_count.* = i;

                        const len = length.codec.decode(reader, null, config, null) catch |err| switch (err) {
                            error.OutOfMemory => unreachable,
                            else => |e| return e,
                        };

                        if (!skip) {
                            try value.ensureTotalCapacity(gpa, len);

                            const original_count = value.count();
                            for (
                                value.keys()[0..@min(len, original_count)],
                                value.values()[0..@min(len, original_count)],
                            ) |*k, *v| {
                                try key.decodeIntoOne(reader, gpa, config, k, key_ctx);
                                try val.decodeIntoOne(reader, gpa, config, v, val_ctx);
                            }

                            if (len < original_count) {
                                key.freeMany(gpa, value.keys()[len..], key_ctx);
                                val.freeMany(gpa, value.values()[len..], val_ctx);
                                value.shrinkRetainingCapacity(len);
                            }

                            value.reIndex(gpa) catch |err| {
                                freeKeysAndVals(gpa, value, maybe_ctx);
                                value.clearRetainingCapacity();
                                return err;
                            };

                            if (len > original_count) for (original_count..len) |_| {
                                const k = try key.decode(reader, gpa, config, key_ctx);
                                errdefer key.free(gpa, &k, key_ctx);

                                const v = try val.decode(reader, gpa, config, val_ctx);
                                errdefer val.free(gpa, &v, val_ctx);

                                if (value.contains(k)) return error.DecodeFailed;
                                value.putAssumeCapacity(k, v);
                            };
                        } else {
                            try entry_codec.decodeSkip(reader, config, len, .{ key_ctx, val_ctx });
                        }
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    values: []const Map,
                    maybe_ctx: DecodeCtxParam,
                ) void {
                    const gpa = gpa_opt.?;
                    for (values) |*value| {
                        freeKeysAndVals(gpa, value, maybe_ctx);
                        var copy = value.*;
                        copy.deinit(gpa);
                    }
                }

                fn freeKeysAndVals(
                    gpa: std.mem.Allocator,
                    value: *const Map,
                    maybe_ctx: DecodeCtxParam,
                ) void {
                    if (key.freeFn == null and val.freeFn == null) return;
                    const key_ctx, const val_ctx = unwrapKeyValCtxs(.decode, maybe_ctx);
                    key.freeMany(gpa, value.keys(), key_ctx);
                    val.freeMany(gpa, value.values(), val_ctx);
                }

                fn unwrapKeyValCtxs(
                    comptime which: enum { encode, decode },
                    maybe_ctx: anytype,
                ) switch (which) {
                    .encode => struct { key.EncodeCtx, val.EncodeCtx },
                    .decode => struct { key.DecodeCtx, val.DecodeCtx },
                } {
                    const KeyCtx, const ValCtx = switch (which) {
                        .encode => .{ key.EncodeCtx, val.EncodeCtx },
                        .decode => .{ key.DecodeCtx, val.DecodeCtx },
                    };

                    const key_ctx: KeyCtx = ctx: {
                        const ctx = switch (@typeInfo(KeyCtx)) {
                            .void => break :ctx {},
                            .optional => maybe_ctx orelse break :ctx null,
                            else => maybe_ctx,
                        };
                        break :ctx ctx.key;
                    };
                    const val_ctx: ValCtx = ctx: {
                        const ctx = switch (@typeInfo(ValCtx)) {
                            .void => break :ctx {},
                            .optional => maybe_ctx orelse break :ctx null,
                            else => maybe_ctx,
                        };
                        break :ctx ctx.val;
                    };
                    return .{ key_ctx, val_ctx };
                }
            }));
        }

        /// The `Child` of `V`. Corresponds to `Child` in all of the following,
        /// and all permutations of their cv-qualified forms: `?C`, `*C`.
        pub const Child = switch (@typeInfo(V)) {
            .optional => |optional_info| optional_info.child,
            .pointer => |ptr_info| switch (ptr_info.size) {
                .one => ptr_info.child,
                else => @compileError(@typeName(V) ++ " does not have a child type."),
            },
            else => @compileError(@typeName(V) ++ " does not have a child type."),
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
            .pointer => |ptr_info| switch (ptr_info.size) {
                .one => switch (@typeInfo(ptr_info.child)) {
                    .array => |array_info| array_info.child,
                    else => @compileError(@typeName(V) ++ " is not a valid indexable pointer."),
                },
                .slice => ptr_info.child,
                .many => ptr_info.child,
                else => @compileError(@typeName(V) ++ " is not a valid indexable pointer."),
            },
            else => @compileError(@typeName(V) ++ " is not a valid indexable pointer or array."),
        };

        /// A struct with the same set of field names as `V` (a struct or a union), wherein each field
        /// has a type `StdCodec(@FieldType(V, field_name))`, where `field_name` is the corresponding name
        /// of the field.
        /// If `V` is a tuple, this is also a tuple.
        pub const Fields = @Type(.{
            .@"struct" = switch (@typeInfo(V)) {
                inline .@"struct", .@"union" => |info, tag| s_info: {
                    const is_tuple = tag == .@"struct" and info.is_tuple;
                    var new_fields: [info.fields.len]std.builtin.Type.StructField = undefined;
                    for (&new_fields, info.fields) |*new_field, s_field| {
                        const FieldType = StdCodec(s_field.type);
                        new_field.* = .{
                            .name = s_field.name,
                            .type = FieldType,
                            .default_value_ptr = null,
                            .is_comptime = false,
                            .alignment = @alignOf(FieldType),
                        };
                    }
                    const fields_copy = new_fields;
                    break :s_info .{
                        .layout = .auto,
                        .backing_integer = null,
                        .is_tuple = is_tuple,
                        .fields = &fields_copy,
                        .decls = &.{},
                    };
                },
                else => @compileError(@typeName(V) ++ " is not a struct or union."),
            },
        });

        pub fn FieldContexts(field_codecs: Fields) struct {
            type,
            type,
            enum { need_decode_init, no_decode_init },
            enum { need_free, no_free },
            usize, // max_encode_min_size
            usize, // max_encode_stack_size
        } {
            const fields, const is_tuple = switch (@typeInfo(V)) {
                .@"struct" => |s_info| .{ s_info.fields, s_info.is_tuple },
                .@"union" => |u_info| .{ u_info.fields, false },
                else => @compileError("doesn't apply for " ++ @typeName(V)),
            };

            var any_decode_init: bool = false;
            var any_free: bool = false;
            var max_encode_min_size: usize = 0;
            var max_encode_stack_size: usize = 0;

            var enc_field_kind_max: bk.std_reflect.FieldGroupKind = .all_void;
            var encode_fields: [fields.len]std.builtin.Type.StructField = undefined;

            var dec_field_kind_max: bk.std_reflect.FieldGroupKind = .all_void;
            var decode_fields: [fields.len]std.builtin.Type.StructField = undefined;

            @setEvalBranchQuota(fields.len * 5 + 2);
            for (
                fields,
                &encode_fields,
                &decode_fields,
            ) |field, *encode_field, *decode_field| {
                const std_field_codec: bk.Codec(field.type) = @field(field_codecs, field.name).codec;

                any_decode_init = any_decode_init or std_field_codec.decodeInitFn != null;
                any_free = any_free or std_field_codec.freeFn != null;
                max_encode_min_size = @max(max_encode_min_size, std_field_codec.encode_min_size);
                max_encode_stack_size = @max(max_encode_stack_size, std_field_codec.encode_stack_size);

                const enc_field_kind: bk.std_reflect.FieldGroupKind = .fromType(std_field_codec.EncodeCtx);
                enc_field_kind_max = .max(enc_field_kind_max, enc_field_kind);
                encode_field.* = .{
                    .name = field.name,
                    .type = std_field_codec.EncodeCtx,
                    .default_value_ptr = if (enc_field_kind == .all_void) @ptrCast(&{}) else null,
                    .is_comptime = enc_field_kind == .all_void,
                    .alignment = @alignOf(std_field_codec.EncodeCtx),
                };

                const dec_field_kind: bk.std_reflect.FieldGroupKind = .fromType(std_field_codec.DecodeCtx);
                dec_field_kind_max = .max(dec_field_kind_max, dec_field_kind);
                decode_field.* = .{
                    .name = field.name,
                    .type = std_field_codec.DecodeCtx,
                    .default_value_ptr = if (dec_field_kind == .all_void) @ptrCast(&{}) else null,
                    .is_comptime = dec_field_kind == .all_void,
                    .alignment = @alignOf(std_field_codec.DecodeCtx),
                };
            }

            const Enc = @Type(.{ .@"struct" = .{
                .layout = .auto,
                .backing_integer = null,
                .fields = &encode_fields,
                .decls = &.{},
                .is_tuple = is_tuple,
            } });
            const Dec = @Type(.{ .@"struct" = .{
                .layout = .auto,
                .backing_integer = null,
                .fields = &decode_fields,
                .decls = &.{},
                .is_tuple = is_tuple,
            } });

            return .{
                switch (enc_field_kind_max) {
                    .all_void => void,
                    .all_opt_or_void => ?Enc,
                    .some_required => Enc,
                },
                switch (dec_field_kind_max) {
                    .all_void => void,
                    .all_opt_or_void => ?Dec,
                    .some_required => Dec,
                },
                if (any_decode_init) .need_decode_init else .no_decode_init,
                if (any_free) .need_free else .no_free,
                max_encode_min_size,
                max_encode_stack_size,
            };
        }
    };
}

const IndexOfScalarCmp = enum { lt, lteq, gteq, gt };

fn indexOfScalarCmpPos(
    comptime T: type,
    slice: []const T,
    start_index: usize,
    comptime cmp: IndexOfScalarCmp,
    value: T,
) ?usize {
    const builtin = @import("builtin");
    const use_vectors = switch (builtin.zig_backend) {
        // These backends don't support vectors yet.
        .stage2_aarch64,
        .stage2_powerpc,
        .stage2_riscv64,
        => false,
        // The SPIR-V backend does not support the optimized path yet.
        .stage2_spirv => false,
        else => true,
    };

    // The naive memory comparison implementation is more useful for fuzzers to find interesting inputs.
    const use_vectors_for_comparison = use_vectors and !builtin.fuzz;

    if (start_index >= slice.len) return null;

    var i: usize = start_index;
    if (use_vectors_for_comparison and
        !std.debug.inValgrind() and // https://github.com/ziglang/zig/issues/17717
        !@inComptime() and
        (@typeInfo(T) == .int or @typeInfo(T) == .float) and std.math.isPowerOfTwo(@bitSizeOf(T)))
    {
        if (std.simd.suggestVectorLength(T)) |block_len| {
            // For Intel Nehalem (2009) and AMD Bulldozer (2012) or later, unaligned loads on aligned data result
            // in the same execution as aligned loads. We ignore older arch's here and don't bother pre-aligning.
            //
            // Use `std.simd.suggestVectorLength(T)` to get the same alignment as used in this function
            // however this usually isn't necessary unless your arch has a performance penalty due to this.
            //
            // This may differ for other arch's. Arm for example costs a cycle when loading across a cache
            // line so explicit alignment prologues may be worth exploration.

            // Unrolling here is ~10% improvement. We can then do one bounds check every 2 blocks
            // instead of one which adds up.
            const Block = @Vector(block_len, T);
            if (i + 2 * block_len < slice.len) {
                const mask: Block = @splat(value);
                while (true) {
                    inline for (0..2) |_| {
                        const block: Block = slice[i..][0..block_len].*;
                        const matches = switch (cmp) {
                            .lt => block < mask,
                            .lteq => block <= mask,
                            .gteq => block >= mask,
                            .gt => block > mask,
                        };
                        if (@reduce(.Or, matches)) {
                            return i + std.simd.firstTrue(matches).?;
                        }
                        i += block_len;
                    }
                    if (i + 2 * block_len >= slice.len) break;
                }
            }

            // {block_len, block_len / 2} check
            inline for (0..2) |j| {
                const block_x_len = block_len / (1 << j);
                comptime if (block_x_len < 4) break;

                const BlockX = @Vector(block_x_len, T);
                if (i + block_x_len < slice.len) {
                    const mask: BlockX = @splat(value);
                    const block: BlockX = slice[i..][0..block_x_len].*;
                    const matches = switch (cmp) {
                        .lt => block < mask,
                        .lteq => block <= mask,
                        .gteq => block >= mask,
                        .gt => block > mask,
                    };
                    if (@reduce(.Or, matches)) {
                        return i + std.simd.firstTrue(matches).?;
                    }
                    i += block_x_len;
                }
            }
        }
    }

    for (slice[i..], i..) |c, j| {
        const match = switch (cmp) {
            .lt => c < value,
            .lteq => c <= value,
            .gteq => c >= value,
            .gt => c > value,
        };
        if (match) return j;
    }
    return null;
}

inline fn encIntLit(comptime config: bk.Config, comptime int: anytype) []const u8 {
    const Int = if (@TypeOf(int) == usize) u64 else @TypeOf(int);
    comptime return switch (config.int) {
        .fixint => std.mem.toBytes(std.mem.nativeTo(Int, int, config.endian)),
        .varint => bk.varint.encodedLiteral(config.endian, int),
    };
}

inline fn encStrLit(comptime config: bk.Config, comptime str: []const u8) []const u8 {
    comptime return encIntLit(config, @as(usize, str.len)) ++ str;
}

test "empty" {
    var null_reader: std.Io.Reader = .failing;
    var null_writer: std.Io.Writer.Discarding = .init(&.{});
    const void_codec: bk.Codec(void) = .standard(.empty);
    try std.testing.expectEqual({}, void_codec.encode(&null_writer.writer, .default, &{}, {}));
    try std.testing.expectEqual({}, void_codec.decode(&null_reader, null, .default, {}));
    try std.testing.expectEqual(0, void_codec.encodedSize(.default, &{}, {}));
}

test "byte" {
    const byte_codec: bk.Codec(u8) = .standard(.byte);
    try std.testing.expectEqual('f', byte_codec.decodeSliceExact(&.{'f'}, null, .default, {}));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, null, .default, {}));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, null, .default, {}));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeSliceExact(&.{}, null, .default, {}));
    try std.testing.expectError(error.Overlong, byte_codec.decodeSliceExact("bar", null, .default, {}));
    try std.testing.expectEqual(1, byte_codec.encodedSize(.default, &'z', {}));
}

test "bool" {
    const bool_codec: bk.Codec(bool) = .standard(.boolean);
    try std.testing.expectEqual(false, bool_codec.decodeSliceExact(&.{0}, null, .default, null));
    try std.testing.expectEqual(true, bool_codec.decodeSliceExact(&.{1}, null, .default, null));

    var diag: StdCodec(bool).BoolDecodeDiag = .init;
    try std.testing.expectError(error.DecodeFailed, bool_codec.decodeSliceExact(&.{2}, null, .default, &diag));
    try std.testing.expectEqual(2, diag.real_byte);

    try std.testing.expectError(error.EndOfStream, bool_codec.decodeSliceExact(&.{}, null, .default, &diag));
    try std.testing.expectError(error.Overlong, bool_codec.decodeSliceExact(&.{ 1, 0 }, null, .default, &diag));
    try std.testing.expectEqual(1, bool_codec.encodedSize(.default, &false, {}));
    try std.testing.expectEqual(1, bool_codec.encodedSize(.default, &true, {}));
}

test "int" {
    try testEncodedBytesAndRoundTrip(u32, .shallow, .standard(.int), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = 250,
        .permutations = &.{
            .init(.cfg(.little, .varint), &.{250}),
        },
    });
    try testEncodedBytesAndRoundTrip(u32, .shallow, .standard(.int), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = 251,
        .permutations = &.{
            .init(.cfg(.little, .varint), &.{ 251, 251, 0 }),
        },
    });
    try testEncodedBytesAndRoundTrip(u32, .shallow, .standard(.int), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = 300,
        .permutations = &.{
            .init(.cfg(.little, .varint), &.{ 251, 0x2C, 1 }),
        },
    });
    try testEncodedBytesAndRoundTrip(u32, .shallow, .standard(.int), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = std.math.maxInt(u16),
        .permutations = &.{
            .init(.cfg(.little, .varint), &.{ 251, 0xFF, 0xFF }),
        },
    });
    try testEncodedBytesAndRoundTrip(u32, .shallow, .standard(.int), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = std.math.maxInt(u16) + 1,
        .permutations = &.{
            .init(.cfg(.little, .varint), &.{ 252, 0, 0, 1, 0 }),
        },
    });

    try testCodecRoundTrips(i16, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(i16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(u16, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(u16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(i32, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(i32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u32, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(u32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i64, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(i64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u64, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(u64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i128, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(i128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u128, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(u128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i256, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(i256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u256, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(u256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(isize, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(isize) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(usize, .shallow, .standard(.int), {}, null, {}, &intTestEdgeCases(usize) ++ .{ 1, 5, 1000000000, 32, 8 });
}

test "float" {
    try testCodecRoundTrips(f32, .shallow, .standard(.float), {}, {}, {}, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f32, .shallow, .standard(.float), {}, {}, {}, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f64, .shallow, .standard(.float), {}, {}, {}, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f64, .shallow, .standard(.float), {}, {}, {}, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f32, .shallow, .standard(.float), {}, {}, {}, &floatTestEdgeCases(f32));
    try testCodecRoundTrips(f64, .shallow, .standard(.float), {}, {}, {}, &floatTestEdgeCases(f64));
}

test "utf8_codepoint" {
    try std.testing.expectEqual(1, bk.Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{7F}', {}));
    try std.testing.expectEqual(2, bk.Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{ff}', {}));
    try std.testing.expectEqual(3, bk.Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{fff}', {}));
    try std.testing.expectEqual(4, bk.Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{fffff}', {}));
    try testCodecRoundTrips(u8, .shallow, .standard(.utf8_codepoint), {}, {}, {}, &@as([128]u8, std.simd.iota(u8, 128))); // ascii
    inline for (.{ u1, u2, u3, u4, u5, u6, u7, u8, u16, u21, u32 }) |AsciiInt| {
        const max_val = @min(127, std.math.maxInt(AsciiInt));
        const ascii_vals: [max_val + 1]AsciiInt = std.simd.iota(AsciiInt, max_val + 1);
        try testCodecRoundTrips(
            AsciiInt,
            .shallow,
            .standard(.utf8_codepoint),
            {},
            {},
            {},
            &ascii_vals,
        );
    }
    try testCodecRoundTrips(u21, .shallow, .standard(.utf8_codepoint), {}, {}, {}, &.{ 'à', 'á', 'é', 'è', 'ì', 'í', 'ò', 'ó', 'ù', 'ú' });
    try testCodecRoundTrips(u21, .shallow, .standard(.utf8_codepoint), {}, {}, {}, &.{ '\u{2100}', '\u{3100}', '\u{FFAAA}', '\u{FFFFF}', '\u{FFFFF}' });
}

test "optional" {
    try testCodecRoundTrips(?void, .shallow, .standard(.optional(.empty)), {}, null, {}, &.{ null, {}, null, {}, null, {} });
    try testCodecRoundTrips(?bool, .shallow, .standard(.optional(.boolean)), {}, null, {}, &.{
        null, false, null, true, null, true,
        null, false, true, true, null, false,
    });
    try testCodecRoundTrips(?u32, .shallow, .standard(.optional(.int)), {}, null, {}, &.{ null, 4, null, 10000, null, 100000000 });
    try testCodecRoundTrips(?i64, .shallow, .standard(.optional(.int)), {}, null, {}, &.{ null, -7, null, 20000, null, -100000000 });

    const config: bk.Config = .cfg(.little, .varint);
    try testEncodedBytesAndRoundTrip(?u32, .shallow, .standard(.optional(.int)), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = 3,
        .permutations = &.{
            .init(config, "\x01" ++ "\x03"),
        },
    });
    try testEncodedBytesAndRoundTrip(?u32, .shallow, .standard(.optional(.int)), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = null,
        .permutations = &.{
            .init(config, "\x00"),
        },
    });
    try testEncodedBytesAndRoundTrip(?u32, .shallow, .standard(.optional(.int)), .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = 251,
        .permutations = &.{
            .init(config, "\x01" ++ "\xFB\xFB\x00"),
        },
    });
}

test "packedFields" {
    const helper = struct {
        fn IntWrapper(comptime Int: type) type {
            return packed struct(Int) {
                value: Int,
                const IntWrapperSelf = @This();

                const bk_codec: bk.Codec(IntWrapperSelf) = .standard(.packedFields(.int));

                fn from(bits: Int) IntWrapperSelf {
                    return @bitCast(bits);
                }

                const edge_cases: [23]IntWrapperSelf = @bitCast(intTestEdgeCases(Int));

                fn expectEncodedBytesTestRoundTrip(
                    config: bk.Config,
                    original: IntWrapperSelf,
                    expected_bytes: []const u8,
                ) !void {
                    try testEncodedBytesAndRoundTrip(IntWrapperSelf, .shallow, bk_codec, .{
                        .enc_ctx = {},
                        .dec_ctx = null,
                        .cmp_ctx = {},
                        .original = original,
                        .permutations = &.{.init(config, expected_bytes)},
                    });
                }
            };
        }
    };

    const U32Wrapper = helper.IntWrapper(u32);
    try U32Wrapper.expectEncodedBytesTestRoundTrip(.cfg(.little, .varint), .from(250), &.{250});
    try U32Wrapper.expectEncodedBytesTestRoundTrip(.cfg(.little, .varint), .from(251), &.{ 251, 251, 0 });
    try U32Wrapper.expectEncodedBytesTestRoundTrip(.cfg(.little, .varint), .from(300), &.{ 251, 0x2C, 1 });
    try U32Wrapper.expectEncodedBytesTestRoundTrip(.cfg(.little, .varint), .from(std.math.maxInt(u16)), &.{ 251, 0xFF, 0xFF });
    try U32Wrapper.expectEncodedBytesTestRoundTrip(.cfg(.little, .varint), .from(std.math.maxInt(u16) + 1), &.{ 252, 0, 0, 1, 0 });

    inline for (.{
        helper.IntWrapper(i16),
        helper.IntWrapper(u16),
    }) |SmallWrapper| {
        const values = SmallWrapper.edge_cases ++ [_]SmallWrapper{
            .from(1), .from(5), .from(10000), .from(32), .from(8),
        };
        try testCodecRoundTrips(SmallWrapper, .shallow, SmallWrapper.bk_codec, {}, null, {}, &values);
    }
    inline for (.{
        helper.IntWrapper(usize),
        helper.IntWrapper(u32),
        helper.IntWrapper(u64),
        helper.IntWrapper(u128),
        helper.IntWrapper(u256),

        helper.IntWrapper(isize),
        helper.IntWrapper(i32),
        helper.IntWrapper(i64),
        helper.IntWrapper(i128),
        helper.IntWrapper(i256),
    }) |BigWrapper| {
        const values = BigWrapper.edge_cases ++ [_]BigWrapper{
            .from(1), .from(5), .from(1000000000), .from(32), .from(8),
        };
        try testCodecRoundTrips(BigWrapper, .shallow, BigWrapper.bk_codec, {}, null, {}, &values);
    }
}

test "tuple" {
    const S = struct {
        a: u32,
        b: f64,

        const bk_codec: bk.Codec(@This()) = .standard(.tuple(bk_codec_fields));
        const bk_codec_fields: bk.StdCodec(@This()).Fields = .{
            .a = .int,
            .b = .float,
        };
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
    try testCodecRoundTrips(S, .shallow, S.bk_codec, {}, null, {}, &struct_test_edge_cases);

    try testEncodedBytesAndRoundTrip(S, .shallow, S.bk_codec, .{
        .enc_ctx = {},
        .dec_ctx = null,
        .cmp_ctx = {},
        .original = .{ .a = 1, .b = 0 },
        .permutations = &.{
            .init(.cfg(.little, .varint), "\x01" ++ std.mem.toBytes(@as(f64, 0))),
        },
    });
}

test "taggedUnion" {
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

        const bk_codec: bk.Codec(@This()) = .standard(.taggedUnion(null, .{
            .void = .empty,
            .char = .byte,
            .int = .int,
            .float = .float,
            .record = .tuple(.{
                .a = .int,
                .b = .int,
                .c = .discriminant,
            }),
        }));
    };

    try testCodecRoundTrips(U, .shallow, U.bk_codec, {}, null, {}, &.{
        .void,
        .{ .char = 42 },
        .{ .int = 1111111111 },
        .{ .float = -7 },
        .{ .record = .{ .a = 1, .b = 2, .c = .foo } },
    });
}

test "array value" {
    try testCodecRoundTrips([3]u8, .shallow, .standard(.array(.byte)), {}, {}, {}, &.{ "foo".*, "bar".*, "baz".* });

    try testCodecRoundTrips([2]u64, .shallow, .standard(.array(.int)), {}, null, {}, &.{ .{ 0, 0 }, .{ 0, 1 } });

    try testCodecRoundTrips([2]u64, .shallow, .standard(.array(.int)), {}, null, {}, @ptrCast(&intTestEdgeCases(u64) ++ intTestEdgeCases(u64)));
    try testCodecRoundTrips([2]u64, .shallow, .standard(.array(.int)), {}, null, {}, &.{
        .{ 1, 2 },
        .{ 61, 313131 },
        @splat(111111111),
    });

    try testCodecRoundTrips([2]f32, .shallow, .standard(.array(.float)), {}, {}, {}, @ptrCast(&floatTestEdgeCases(f32) ++ floatTestEdgeCases(f32)));
    try testCodecRoundTrips([2]f64, .shallow, .standard(.array(.float)), {}, {}, {}, @ptrCast(&floatTestEdgeCases(f64) ++ floatTestEdgeCases(f64)));
    try testCodecRoundTrips([2]f32, .shallow, .standard(.array(.float)), {}, {}, {}, &.{
        .{ -1.0, 2 },
        .{ 61, -313131 },
        @splat(111111111.0),
    });
}

test "singleItemPtr" {
    try testCodecRoundTrips(*const u32, .deep, .standard(.singleItemPtr(.int)), {}, null, {}, &.{
        &0, &1, &2, &10000, &std.math.maxInt(u32),
    });

    const u64_codec: bk.Codec(*const u64) = .standard(.singleItemPtr(.int));

    const value: u64 = 72_301;
    var evr_reader_buf: [4096]u8 = undefined;
    var evr_value_buf: [u64_codec.encode_min_size]u8 = undefined;
    var progress_stack: [u64_codec.encode_stack_size]u64 = undefined;
    var evr_state: u64_codec.EncodedReader() = .initOne(&&value, .{
        .reader_buffer = &evr_reader_buf,
        .value_buffer = &evr_value_buf,
        .progress_stack = &progress_stack,
        .config = .cfg(.little, .fixint),
        .ctx = {},
    });
    const evr = &evr_state.interface;

    var foo: u64 = 0;
    var bar: *const u64 = &foo;
    try u64_codec.decodeIntoOne(evr, null, .cfg(.little, .fixint), &bar, null);
}

test "slice value" {
    try testCodecRoundTrips([]const u8, .forSlice(.shallow), .standard(.slice(.byte)), {}, {}, {}, &.{
        &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 }, "foo",  "bar",  "baz",
        &.{ 127, std.math.maxInt(u8) },  "fizz", "buzz", "fizzbuzz",
    });
    try testCodecRoundTrips([]const u32, .forSlice(.shallow), .standard(.slice(.int)), {}, null, {}, &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5, 6 },
        &.{ 7, 8, 9, 10, 11 },
        &.{ 12, 13, 14, 15, 16, 17 },
        &.{ 18, 19, 20, 21, 22, 23, 24 },
        &.{ 25, 26, 27, 28, 29, 30, 31, 32 },
    });
}

test "arrayPtr" {
    try testCodecRoundTrips(*const [3]u32, .forSlice(.shallow), .standard(.arrayPtr(.int)), {}, null, {}, &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5 },
        &.{ 7, 8, 9 },
        &.{ 12, 13, 14 },
        &.{ 18, 19, 20 },
        &.{ 25, 26, 27 },
    });

    try testCodecRoundTrips(*const [3]u8, .forSlice(.shallow), .standard(.arrayPtr(.byte)), {}, {}, {}, &.{
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

test "arrayList" {
    const gpa = std.testing.allocator;

    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try testCodecRoundTrips(std.ArrayList(u8), .forArrayList(.shallow), .standard(.arrayList(.byte)), {}, {}, {}, &.{
        .fromOwnedSlice(try arena.dupe(u8, "")),
        .fromOwnedSlice(try arena.dupe(u8, "foo")),
        .fromOwnedSlice(try arena.dupe(u8, "baz")),
    });

    try testCodecRoundTrips(std.ArrayList(u32), .forArrayList(.shallow), .standard(.arrayList(.int)), {}, null, {}, &.{
        .empty,
        .fromOwnedSlice(try arena.dupe(u32, &.{ 1, 2, 3 })),
        .fromOwnedSlice(try arena.dupe(u32, &intTestEdgeCases(u32))),
    });
    try testEncodedBytesAndRoundTrip(
        std.ArrayList(u16),
        .forArrayList(.shallow),
        .standard(.arrayList(.int)),
        .{
            .enc_ctx = {},
            .dec_ctx = null,
            .cmp_ctx = {},
            .original = .fromOwnedSlice(try arena.dupe(u16, &.{ 0, 1, 250, 251 })),
            .permutations = &.{
                .init(.cfg(.little, .varint), &[_]u8{4} ++ .{0} ++ .{1} ++ .{250} ++ .{ 251, 251, 0 }),
            },
        },
    );

    var list: std.ArrayList([]const u8) = .empty;
    defer list.deinit(gpa);
    defer for (list.items) |str| gpa.free(str);
    try list.ensureTotalCapacityPrecise(gpa, 4);
    const original = try gpa.dupe(u8, "foo");
    list.appendAssumeCapacity(original);
    list.appendAssumeCapacity(try gpa.dupe(u8, "bar"));
    list.appendAssumeCapacity(try gpa.dupe(u8, "baz"));
    list.appendAssumeCapacity(try gpa.dupe(u8, "boo"));

    const str_array_list_codec: bk.Codec(std.ArrayList([]const u8)) = .standard(.arrayList(.slice(.byte)));
    _ = try str_array_list_codec.decodeSliceInto(
        .{2} ++ .{4} ++ "fizz" ++ .{4} ++ "buzz",
        gpa,
        .{ .endian = .little, .int = .varint },
        &list,
        {},
    );
    try std.testing.expectEqualDeep(&[_][]const u8{ "fizz", "buzz" }, list.items);
}

test "arrayHashMap" {
    const gpa = std.testing.allocator;

    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const MapU32U32 = std.AutoArrayHashMapUnmanaged(u32, u32);
    try testCodecRoundTrips(
        MapU32U32,
        .forArrayHashMap(.shallow, .shallow),
        .standard(.arrayHashMap(.int, .int)),
        {},
        null,
        {},
        &.{
            .empty,
            try initArrayHashMap(arena, MapU32U32, &.{ .{ 1, 2 }, .{ 3, 4 } }),
            try initArrayHashMap(arena, MapU32U32, &.{ .{ 5, 6 }, .{ 7, 8 }, .{ 9, 10 } }),
        },
    );

    const MapStrU16 = std.StringArrayHashMapUnmanaged(u16);
    const lev: bk.Config = comptime .cfg(.little, .varint);
    try testEncodedBytesAndRoundTrip(
        MapStrU16,
        .forArrayHashMap(.deep, .shallow),
        .standard(.arrayHashMap(.slice(.byte), .int)),
        .{
            .enc_ctx = {},
            .dec_ctx = null,
            .cmp_ctx = {},
            .original = try initArrayHashMap(arena, MapStrU16, &.{ .{ "foo", 2 }, .{ "bar", 4 } }),
            .permutations = &.{
                .init(lev, encIntLit(lev, 2) ++
                    (encStrLit(lev, "foo") ++ encIntLit(lev, 2)) ++
                    (encStrLit(lev, "bar") ++ encIntLit(lev, 4))),
            },
        },
    );

    var map: MapStrU16 = .empty;
    defer map.deinit(gpa);
    defer for (map.keys()) |str| gpa.free(str);
    try map.ensureTotalCapacity(gpa, 4);

    map.putAssumeCapacity(try gpa.dupe(u8, "foo"), 100);
    map.putAssumeCapacity(try gpa.dupe(u8, "bar"), 150);
    map.putAssumeCapacity(try gpa.dupe(u8, "baz"), 200);
    map.putAssumeCapacity(try gpa.dupe(u8, "fizz"), 250);
    map.putAssumeCapacity(try gpa.dupe(u8, "buzz"), 300);

    const map_str_u16_codec: bk.Codec(MapStrU16) =
        .standard(.arrayHashMap(.slice(.byte), .int));
    _ = try map_str_u16_codec.decodeSliceInto(
        encIntLit(lev, 2) ++
            (encStrLit(lev, "big") ++ encIntLit(lev, 350)) ++
            (encStrLit(lev, "small") ++ encIntLit(lev, 400)),
        gpa,
        lev,
        &map,
        null,
    );
    try std.testing.expectEqualDeep(&[_][]const u8{ "big", "small" }, map.keys());
    try std.testing.expectEqualSlices(u16, &.{ 350, 400 }, map.values());

    _ = try map_str_u16_codec.decodeSliceInto(
        encIntLit(lev, 4) ++
            (encStrLit(lev, "a") ++ encIntLit(lev, 450)) ++
            (encStrLit(lev, "bc") ++ encIntLit(lev, 500)) ++
            (encStrLit(lev, "def") ++ encIntLit(lev, 550)) ++
            (encStrLit(lev, "ghij") ++ encIntLit(lev, 600)),
        gpa,
        lev,
        &map,
        null,
    );
    try std.testing.expectEqualDeep(&[_][]const u8{ "a", "bc", "def", "ghij" }, map.keys());
    try std.testing.expectEqualSlices(u16, &.{ 450, 500, 550, 600 }, map.values());
}

fn initArrayHashMap(
    gpa: std.mem.Allocator,
    comptime Hm: type,
    key_vals: []const blk: {
        const hm_info = bk.std_reflect.ArrayHashMapInfo.from(Hm) orelse
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
    const config: bk.Config = .{ .endian = .little, .int = .varint };
    const overlong_varint_src = [_]u8{ 250, 1 };
    try std.testing.expectEqual(
        250,
        bk.Codec(u32).standard(.int).decodeSliceExact((&overlong_varint_src)[0..1], null, config, null),
    );
    try std.testing.expectError(
        error.Overlong,
        bk.Codec(u32).standard(.int).decodeSliceExact(&overlong_varint_src, null, config, null),
    );
    try std.testing.expectEqual(
        250,
        bk.Codec(u32).standard(.int).decodeSliceIgnoreLength(&overlong_varint_src, null, config, null),
    );
}

test "optional slice memory re-use" {
    const gpa = std.testing.allocator;

    const codec: bk.Codec(?[]const u8) = .standard(.optional(.slice(.byte)));

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
        a: std.ArrayList(u8),
        b: []const u8,

        const bk_codec: bk.Codec(@This()) = .standard(.taggedUnion(.a, .{
            .a = .arrayList(.byte),
            .b = .slice(.byte),
        }));
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

fn TestEncodedBytesAndRoundTripParams(
    comptime T: type,
    codec: bk.Codec(T),
    comparator: testing.Comparator(T),
) type {
    return struct {
        enc_ctx: codec.EncodeCtx,
        dec_ctx: codec.DecodeCtx,
        cmp_ctx: comparator.Ctx,
        original: T,
        permutations: []const Permutation,

        const Permutation = struct {
            config: bk.Config,
            expected_bytes: []const u8,

            fn init(config: bk.Config, expected_bytes: []const u8) Permutation {
                return .{ .config = config, .expected_bytes = expected_bytes };
            }
        };
    };
}

/// Test that `value` encodes into the same bytes as `expected`, and then
/// also test whether `expected` decodes back into the same as `value`.
fn testEncodedBytesAndRoundTrip(
    comptime T: type,
    compare_ctx: testing.Comparator(T),
    codec: bk.Codec(T),
    params: TestEncodedBytesAndRoundTripParams(T, codec, compare_ctx),
) !void {
    const gpa = std.testing.allocator;

    var encoded_buffer: std.Io.Writer.Allocating = .init(gpa);
    defer encoded_buffer.deinit();

    for (params.permutations) |permutation| {
        defer encoded_buffer.clearRetainingCapacity();
        try codec.encode(
            &encoded_buffer.writer,
            permutation.config,
            &params.original,
            params.enc_ctx,
        );
        const actual_bytes = encoded_buffer.written();
        try std.testing.expectEqualSlices(u8, permutation.expected_bytes, actual_bytes);

        const actual_value = codec.decodeSliceExact(actual_bytes, gpa, permutation.config, params.dec_ctx);
        defer if (actual_value) |*unwrapped| codec.free(gpa, unwrapped, params.dec_ctx) else |_| {};

        const err_compare_ctx: testing.Comparator(anyerror!T) = .forErrorUnion(compare_ctx);
        try err_compare_ctx.withCtx(params.cmp_ctx).expectEqual(params.original, actual_value);
    }
}

fn testCodecRoundTrips(
    comptime T: type,
    comparator: testing.Comparator(T),
    codec: bk.Codec(T),
    enc_ctx: codec.EncodeCtx,
    dec_ctx: codec.DecodeCtx,
    cmp_ctx: comparator.Ctx,
    values: []const T,
) !void {
    const err_comparator: testing.Comparator(anyerror!T) = .forErrorUnion(comparator);
    const err_comparator_wc = err_comparator.withCtx(cmp_ctx);

    var buffer: std.ArrayList(u8) = .empty;
    defer buffer.deinit(std.testing.allocator);

    const cfg_permutations = [_]bk.Config{
        .{ .int = .varint, .endian = .little },
        .{ .int = .varint, .endian = .big },
        .{ .int = .fixint, .endian = .little },
        .{ .int = .fixint, .endian = .big },
    };
    for (cfg_permutations) |config| {
        errdefer std.log.err("Error occurred using config: {}", .{config});
        {
            buffer.clearRetainingCapacity();
            var encoded_writer_state: std.Io.Writer.Allocating = .fromArrayList(std.testing.allocator, &buffer);
            defer buffer = encoded_writer_state.toArrayList();
            const encoded_writer: *std.Io.Writer = &encoded_writer_state.writer;
            try codec.encodeMany(encoded_writer, config, values, enc_ctx);
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
            try err_comparator_wc.expectEqual(expected, actual);
        }
        try std.testing.expectEqual(0, encoded_reader.bufferedLen());

        encoded_reader = .fixed(buffer.items);
        var decoded_count: usize = 0;
        try std.testing.expectEqual({}, codec.decodeSkipManyRaw(
            &encoded_reader,
            config,
            values.len,
            &decoded_count,
            dec_ctx,
        ));
        try std.testing.expectEqual(values.len, decoded_count);

        var bvr_reader_buf: [64]u8 = undefined;
        var bvr_value_buf: [codec.encode_min_size]u8 = undefined;
        var bvr_progress_stack: [codec.encode_stack_size]u64 = @splat(0);
        var bvr_state: codec.EncodedReader() = .initMany(values, .{
            .reader_buffer = &bvr_reader_buf,
            .value_buffer = &bvr_value_buf,
            .progress_stack = &bvr_progress_stack,
            .config = config,
            .ctx = enc_ctx,
        });
        const bvr = &bvr_state.interface;

        for (values, 0..) |expected, i| {
            const actual = codec.decode(
                bvr,
                std.testing.allocator,
                config,
                dec_ctx,
            );
            defer if (actual) |*unwrapped| {
                codec.free(std.testing.allocator, unwrapped, dec_ctx);
            } else |_| {};
            errdefer std.log.err("[{d}]: expected '{any}', actual: '{any}'", .{ i, expected, actual });
            try err_comparator_wc.expectEqual(expected, actual);
        }
    }
}

fn Pointer(
    comptime size: std.builtin.Type.Pointer.Size,
    comptime attributes: struct {
        @"const": bool = false,
        @"volatile": bool = false,
        @"allowzero": bool = false,
        @"addrspace": ?std.builtin.AddressSpace = null,
        @"align": ?usize = null,
    },
    comptime Element: type,
    comptime sentinel_opt: ?Element,
) type {
    return @Type(.{
        .pointer = .{
            .size = size,
            .is_const = attributes.@"const",
            .is_volatile = attributes.@"volatile",
            .alignment = attributes.@"align" orelse @alignOf(Element),
            .address_space = attributes.@"addrspace" orelse @typeInfo(*const Element).pointer.address_space,
            .child = Element,
            .is_allowzero = attributes.@"allowzero",
            .sentinel_ptr = if (sentinel_opt) |*s| s else null,
        },
    });
}

const std = @import("std");
const bk = @import("binkode.zig");
const ArrayHashMapInfo = @import("utils/ArrayHashMapInfo.zig");

pub fn StdCodec(comptime V: type) type {
    if (V == noreturn) unreachable;
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
        pub const empty: StdCodecSelf = .implement(void, void, struct {
            comptime {
                if (@sizeOf(V) != 0) @compileError(
                    "void codec is not implemented for type " ++ @typeName(V) ++
                        " of size " ++ std.fmt.comptimePrint("{d}", .{@sizeOf(V)}),
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                value: *const V,
                ctx: void,
            ) bk.EncodeWriterError!void {
                _ = ctx;
                _ = writer;
                _ = config;
                _ = value;
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                gpa_opt: ?std.mem.Allocator,
                value: *V,
                ctx: void,
            ) bk.DecodeReaderError!void {
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
        pub const byte: StdCodec(u8) = .implement(void, void, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                _: bk.Config,
                value: *const u8,
                _: void,
            ) bk.EncodeWriterError!void {
                try writer.writeByte(value.*);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: bk.Config,
                _: ?std.mem.Allocator,
                value: *u8,
                _: void,
            ) bk.DecodeReaderError!void {
                try reader.readSliceAll(value[0..1]);
            }

            pub const free = null;
        });

        pub const BoolDecodeDiag = struct {
            /// Value of the actual decoded byte with an erroneous value.
            /// Only set when `error.DecodeFailed` is returned.
            real_byte: ?u8,

            pub const init: BoolDecodeDiag = .{ .real_byte = null };
        };

        /// Standard codec for a boolean.
        /// Never fails to encode.
        /// Failure to decode indicates a byte value other than 0 or 1.
        /// Decode's initial state is write-only.
        pub const boolean: StdCodec(bool) = .implement(void, ?*BoolDecodeDiag, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                _: bk.Config,
                value: *const bool,
                _: void,
            ) bk.EncodeWriterError!void {
                try writer.writeByte(@intFromBool(value.*));
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: bk.Config,
                _: ?std.mem.Allocator,
                value: *bool,
                maybe_diag: ?*BoolDecodeDiag,
            ) bk.DecodeReaderError!void {
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
        pub const int: StdCodecSelf = .implement(void, ?*IntDecodeDiag, struct {
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
                value: *const V,
                _: void,
            ) bk.EncodeWriterError!void {
                switch (config.int) {
                    .fixint => {
                        try writer.writeInt(V, value.*, config.endian);
                    },
                    .varint => {
                        const unsigned_int = switch (signedness) {
                            .signed => bk.varint.zigzag.signedToUnsigned(Int, value.*),
                            .unsigned => value.*,
                        };
                        var buffer: [bk.varint.IntKind.fullEncodedLen(.maximum)]u8 = undefined;
                        const int_kind = bk.varint.encode(unsigned_int, &buffer, config.endian);
                        try writer.writeAll(buffer[0..int_kind.fullEncodedLen()]);
                    },
                }
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                value: *V,
                maybe_diag: ?*IntDecodeDiag,
            ) bk.DecodeReaderError!void {
                switch (config.int) {
                    .fixint => {
                        var int_bytes: [@sizeOf(Int)]u8 = undefined;
                        try reader.readSliceAll(&int_bytes);
                        const decoded_int = std.mem.readInt(Int, &int_bytes, config.endian);
                        if (std.math.minInt(V) > decoded_int or decoded_int > std.math.maxInt(V)) {
                            if (maybe_diag) |diag| diag.raw_int = decoded_int;
                            return error.DecodeFailed;
                        }
                        value.* = @intCast(decoded_int);
                    },
                    .varint => {
                        const raw_int = try bk.varint.decodeReader(reader, config.endian);
                        switch (signedness) {
                            .unsigned => {
                                if (raw_int > std.math.maxInt(V)) {
                                    if (maybe_diag) |diag| diag.raw_int = raw_int;
                                    return error.DecodeFailed;
                                }
                                value.* = @intCast(raw_int);
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
                                value.* = @intCast(decoded_int);
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
        pub const float: StdCodecSelf = .implement(void, void, struct {
            const AsInt = std.meta.Int(.unsigned, @bitSizeOf(V));
            comptime {
                switch (V) {
                    f32, f64 => {},
                    else => @compileError("float codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                value: *const V,
                _: void,
            ) bk.EncodeWriterError!void {
                const as_int_endian = std.mem.nativeTo(AsInt, @bitCast(value.*), config.endian);
                try writer.writeAll(@ptrCast(&as_int_endian));
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) bk.DecodeReaderError!void {
                try reader.readSliceAll(@ptrCast(value));
                value.* = @bitCast(std.mem.nativeTo(AsInt, @bitCast(value.*), config.endian));
            }

            pub const free = null;
        });

        /// Standard codec for a UTF-8 codepoint.
        /// Failure to encode indicates an invalid codepoint value.
        /// Failure to decode indicates an invalid codepoint value.
        /// Decode's initial state is write-only.
        pub const utf8_codepoint: StdCodecSelf = .implement(void, void, struct {
            comptime {
                switch (V) {
                    u1, u2, u3, u4, u5, u6, u7 => {},
                    u8, u16, u21, u32 => {},
                    else => @compileError("char codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(
                writer: *std.Io.Writer,
                _: bk.Config,
                value: *const V,
                _: void,
            ) bk.EncodeWriterError!void {
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
                _: bk.Config,
                _: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) bk.DecodeReaderError!void {
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
        pub fn optional(payload_codec: StdCodec(Child)) StdCodecSelf {
            return .optionalNonStd(.standard(payload_codec));
        }

        /// Same as `optional`, but directly accepting a non-standard `payload_codec`.
        /// Facilitates composition with non-standard codecs.
        pub fn optionalNonStd(payload: bk.Codec(Child)) StdCodecSelf {
            const EncodeCtx = payload.EncodeCtx;
            const DecodeCtx = OptionalDecodeCtx(payload.DecodeCtx);

            const decode_ctx_opt = switch (@typeInfo(payload.DecodeCtx)) {
                .void, .optional => true,
                else => false,
            };
            const DecodeCtxParam = if (decode_ctx_opt) ?DecodeCtx else DecodeCtx;

            const erased = ImplementMethods(EncodeCtx, DecodeCtxParam, struct {
                const Unwrapped = @typeInfo(V).optional.child;

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const V,
                    ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    boolean.codec.encode(writer, config, &(value.* != null), ctx) catch |err| switch (err) {
                        error.WriteFailed => |e| return e,
                        error.EncodeFailed => unreachable, // bool never fails to encode
                    };
                    const payload_ptr = if (value.*) |*unwrapped| unwrapped else return;
                    try payload.encode(writer, config, payload_ptr, {});
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
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeReaderError!void {
                    const ctx: DecodeCtx = ctx: {
                        if (!decode_ctx_opt) break :ctx maybe_ctx;
                        break :ctx maybe_ctx orelse .{
                            .diag = null,
                            .pl = if (payload.DecodeCtx != void) null,
                        };
                    };
                    const is_some = try boolean.codec.decode(reader, null, config, ctx.diag);
                    if (is_some) {
                        if (payload.decodeInitFn == null or value.* == null) {
                            value.* = @as(Unwrapped, undefined);
                            try payload.decodeInitOne(gpa_opt, &value.*.?, ctx.pl);
                        }
                        try payload.decodeInto(reader, gpa_opt, config, &value.*.?, ctx.pl);
                    } else {
                        if (payload.decodeInitFn != null) if (value.*) |*pl| {
                            payload.free(gpa_opt, pl, ctx.pl);
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
                    payload.free(ctx.pl, gpa_opt, unwrapped);
                }
            });

            return .from(.{
                .EncodeCtx = EncodeCtx,
                .encodeFn = erased.encode,

                .DecodeCtx = DecodeCtxParam,
                .decodeInitFn = if (payload.decodeInitFn != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (payload.freeFn != null) erased.free else null,
            });
        }

        pub fn TupleEncodeCtx(field_codecs: Fields) type {
            const EncodeCtx, _, _, _ = FieldContexts(field_codecs);
            return EncodeCtx;
        }

        pub fn TupleDecodeCtx(field_codecs: Fields) type {
            _, const DecodeCtx, _, _ = FieldContexts(field_codecs);
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
            const free_req //
            = FieldContexts(field_codecs);

            const any_decode_init = decode_init_req == .need_decode_init;
            const any_free = free_req == .need_free;

            const erased = ImplementMethods(EncodeCtx, DecodeCtx, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const V,
                    ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    inline for (s_fields) |s_field| {
                        const field: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                        const field_ctx = getFieldCtx(ctx, s_field.name, field.codec.EncodeCtx);
                        const field_ptr = &@field(value, s_field.name);
                        try field.codec.encode(writer, config, field_ptr, field_ctx);
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
                            const field_codec: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                            const field_ctx = getFieldCtx(ctx, s_field.name);
                            const field_ptr = &@field(value, s_field.name);
                            try field_codec.decodeInitOne(field_ctx, gpa_opt, field_ptr);
                        }
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    ctx: DecodeCtx,
                ) bk.DecodeReaderError!void {
                    inline for (s_fields, 0..) |s_field, i| {
                        errdefer freeFieldSubset(i, gpa_opt, value, ctx);
                        const field: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                        const field_ctx = getFieldCtx(ctx, s_field.name, field.codec.DecodeCtx);
                        const field_ptr = &@field(value, s_field.name);
                        try field.codec.decodeInto(reader, gpa_opt, config, field_ptr, field_ctx);
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
                    maybe_ctx: DecodeCtx,
                ) void {
                    inline for (s_fields[0..n_fields_to_deinit]) |s_field| {
                        const field: StdCodec(s_field.type) = @field(field_codecs, s_field.name);
                        const field_ctx = getFieldCtx(maybe_ctx, s_field.name, field.codec.DecodeCtx);
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

                .DecodeCtx = DecodeCtx,
                .decodeInitFn = if (any_decode_init) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (any_free) erased.free else null,
            });
        }

        pub fn TaggedUnionDecodeCtx(
            payload_codecs: Fields,
        ) type {
            _, const PayloadDecodeCtx, _, _ = FieldContexts(payload_codecs);
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
            /// It should also be noted that under this configuration, if the decoded TODO
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
            const free_req //
            = FieldContexts(payload_codecs);
            const DecodeCtx = TaggedUnionDecodeCtxGeneric(PayloadDecodeCtx);

            const pl_field_kind: FieldGroupKind = .fromType(@FieldType(DecodeCtx, "pl"));
            const any_free = free_req == .need_free;

            const DecodeCtxParam = switch (pl_field_kind) {
                .all_void, .all_opt_or_void => ?DecodeCtx,
                .some_required => DecodeCtx,
            };

            const erased = ImplementMethods(EncodeCtx, DecodeCtxParam, struct {
                const TaggedUnionImpl = @This();
                const std_tag: StdCodec(Tag) = .discriminant;

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const V,
                    maybe_ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    const current_tag: union_info.tag_type.? = value.*;
                    try std_tag.codec.encode(writer, config, &current_tag, {});
                    switch (value.*) {
                        inline else => |*payload_ptr, itag| {
                            const Payload = @TypeOf(payload_ptr.*);
                            const payload_codec: StdCodec(Payload) = @field(payload_codecs, @tagName(itag));
                            const payload_ctx: payload_codec.codec.EncodeCtx = ctx: {
                                const ctx = switch (@typeInfo(payload_codec.codec.EncodeCtx)) {
                                    .void => break :ctx {},
                                    .optional => maybe_ctx orelse break :ctx null,
                                    else => maybe_ctx,
                                };
                                break :ctx @field(ctx, @tagName(itag));
                            };

                            try payload_codec.codec.encode(writer, config, payload_ptr, payload_ctx);
                        },
                    }
                }

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
                    value: *V,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeReaderError!void {
                    const valid_init_state = comptime decode_init_tag_opt != null;
                    const ctx: DecodeCtx = unwrapMaybeCtx(maybe_ctx);
                    switch (try std_tag.codec.decode(reader, null, config, ctx.diag)) {
                        inline else => |decoded_tag| {
                            const Payload = @FieldType(V, @tagName(decoded_tag));
                            const payload: StdCodec(Payload) = @field(payload_codecs, @tagName(decoded_tag));
                            const payload_ctx: payload.codec.DecodeCtx = getPlCtx(ctx, @tagName(decoded_tag), payload.codec.DecodeCtx);

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
                                if (any_free) TaggedUnionImpl.free(gpa_opt, value, ctx);
                                value.* = @unionInit(V, @tagName(decoded_tag), payload_val);
                            }

                            const payload_ptr = &@field(value, @tagName(decoded_tag));
                            try payload.codec.decodeInto(reader, gpa_opt, config, payload_ptr, payload_ctx);
                        },
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    maybe_ctx: DecodeCtxParam,
                ) void {
                    comptime if (!any_free) unreachable;
                    const ctx: DecodeCtx = unwrapMaybeCtx(maybe_ctx);
                    switch (value.*) {
                        inline else => |*payload_ptr, itag| {
                            const Payload = @FieldType(V, @tagName(itag));
                            const payload: StdCodec(Payload) = @field(payload_codecs, @tagName(itag));
                            const payload_ctx: payload.codec.DecodeCtx = getPlCtx(ctx, @tagName(itag), payload.codec.DecodeCtx);
                            payload.codec.free(gpa_opt, payload_ptr, payload_ctx);
                        },
                    }
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

                .DecodeCtx = DecodeCtxParam,
                .decodeInitFn = if (decode_init_tag_opt != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
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
        pub const discriminant: StdCodecSelf = .implement(void, ?*DiscriminantDecodeCtx, struct {
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
                value: *const V,
                _: void,
            ) bk.EncodeWriterError!void {
                const as_u32: u32 = @intFromEnum(value.*);
                return u32_codec.encode(writer, config, &as_u32, {});
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                _: ?std.mem.Allocator,
                value: *V,
                maybe_diag: ?*DiscriminantDecodeCtx,
            ) bk.DecodeReaderError!void {
                const as_u32 = try u32_codec.decode(reader, null, config, null);
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
        /// Optimization over `array(&.byte)`.
        /// Decode's initial state is write-only.
        pub const byte_array: StdCodecSelf = .implement(void, void, struct {
            pub fn encode(
                writer: *std.Io.Writer,
                _: bk.Config,
                value: *const V,
                _: void,
            ) bk.EncodeWriterError!void {
                try writer.writeAll(value);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: bk.Config,
                _: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) bk.DecodeReaderError!void {
                try reader.readSliceAll(value);
            }

            pub const free = null;
        });

        /// Standard codec for an array.
        /// Allocation requirement defined by element codec.
        /// Decode's initial state is defined as an array of initial states conforming to `element_codec`'s expectations.
        /// Also see `byte_array`.
        pub fn array(element: StdCodec(Element)) StdCodecSelf {
            const EncodeCtx = element.codec.EncodeCtx;
            const DecodeCtx = element.codec.DecodeCtx;
            const erased = ImplementMethods(EncodeCtx, DecodeCtx, struct {
                const not_implemented_err_msg = "array codec not is not implemented for type " ++ @typeName(V);

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const V,
                    ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| try element.codec.encode(writer, config, elem, ctx),
                        .vector => |vec_info| for (0..vec_info.len) |i| try element.codec.encode(writer, config, &value[i], ctx),
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                    ctx: element.DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    switch (@typeInfo(V)) {
                        .array => try element.decodeInitMany(gpa_opt, @ptrCast(values), ctx), // flatten `[][n]E` as `[]E`.
                        .vector => |vec_info| for (values) |*value| {
                            var arr: [vec_info.len]Element = value.*;
                            try element.decodeInitMany(gpa_opt, &arr, ctx);
                            value.* = arr;
                        },
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    ctx: DecodeCtx,
                ) bk.DecodeReaderError!void {
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| try element.codec.decodeInto(reader, gpa_opt, config, elem, ctx),
                        .vector => |vec_info| for (0..vec_info.len) |i| try element.codec.decodeInto(reader, gpa_opt, config, &value[i], ctx),
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: element.DecodeCtx,
                ) void {
                    if (element.freeFn == null) return;
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| element.free(gpa_opt, elem, ctx),
                        .vector => |vec_info| for (0..vec_info.len) |i| element.free(gpa_opt, &value[i], ctx),
                        else => @compileError(not_implemented_err_msg),
                    }
                }
            });

            return .from(.{
                .EncodeCtx = element.codec.EncodeCtx,
                .encodeFn = erased.encode,

                .DecodeCtx = element.codec.DecodeCtx,
                .decodeInitFn = if (element.codec.decodeInitFn != null) erased.decodeInit else null,
                .decodeFn = erased.decode,
                .freeFn = if (element.codec.freeFn != null) erased.free else null,
            });
        }

        /// Standard codec for a single item pointer.
        /// Decoding allocates the result.
        /// Disallows `Child = [n]T` and `Child = @Vector(n, T)`, see `arrayPtr` instead.
        pub fn singleItemPtr(child: StdCodec(Child)) StdCodecSelf {
            const EncodeCtx = child.codec.EncodeCtx;
            const DecodeCtx = child.codec.DecodeCtx;
            return .implement(EncodeCtx, DecodeCtx, struct {
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
                    value: *const V,
                    ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    try child.codec.encode(writer, config, value.*, ctx);
                }

                pub const decodeInit = null;

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    ctx: DecodeCtx,
                ) bk.DecodeReaderError!void {
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
                    try child.codec.decodeInto(reader, gpa, config, ptr, ctx);
                    value.* = ptr;
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    child.codec.free(gpa, value.*, ctx);
                    gpa.destroy(value.*);
                }
            });
        }

        /// Standard codec for a byte slice. Encodes the length. Optimization over `slice(&.byte)`.
        /// Requires allocation.
        ///
        /// Decode's initial state is `&.{}`. If it is non-empty, it must have been allocated using
        /// the supplied `gpa_opt.?`; it will be resized to the decoded length if necessary, and the
        /// contents will be overwritten with the contents read from the stream - the pointed-to bytes
        /// are assumed to be write-only during the duration of the function.
        /// Allocation failure while doing so may result in destruction of the original allocation,
        /// setting it to empty.
        pub const byte_slice: StdCodecSelf = .implement(void, void, struct {
            const ptr_info = @typeInfo(V).pointer;
            comptime {
                if (ptr_info.size != .slice) @compileError(
                    "single item ptr codec is not implemented for type " ++ @typeName(V),
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                value: *const V,
                _: void,
            ) bk.EncodeWriterError!void {
                try length.codec.encode(writer, config, &value.len, {});
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
                config: bk.Config,
                gpa_opt: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) bk.DecodeReaderError!void {
                const gpa = gpa_opt.?;

                const len = try length.codec.decode(reader, null, config, null);
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
        /// Also see `byte_array`.
        pub fn slice(element: StdCodec(Element)) StdCodecSelf {
            const EncodeCtx = element.codec.EncodeCtx;
            const DecodeCtx = element.codec.DecodeCtx;
            return .implement(EncodeCtx, DecodeCtx, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .slice) @compileError(
                        "single item ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const V,
                    ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    try length.codec.encode(writer, config, &value.len, {});
                    for (value.*) |*elem| try element.codec.encode(writer, config, elem, ctx);
                }

                pub const decodeInit = null;

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    ctx: DecodeCtx,
                ) bk.DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const len = try length.codec.decode(reader, null, config, null);
                    const result = try gpa.alignedAlloc(ptr_info.child, .fromByteUnits(ptr_info.alignment), len);
                    errdefer gpa.free(result);

                    for (result, 0..) |*elem, i| {
                        errdefer if (element.codec.freeFn != null) {
                            for (result[0..i]) |*prev| element.free(gpa, prev, ctx);
                        };
                        try element.codec.decodeInto(reader, gpa, config, elem, ctx);
                    }
                    value.* = result;
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    if (element.codec.freeFn != null) {
                        for (value.*) |*elem| element.free(gpa, elem, ctx);
                    }
                    gpa.free(value.*);
                }
            });
        }

        /// Standard codec for a byte array pointer. Encodes the length. Optimization over `arrayPtr(&.byte)`.
        /// Requires allocation.
        pub const byte_array_ptr: StdCodecSelf = .implement(void, void, struct {
            const ptr_info = @typeInfo(V).pointer;
            comptime {
                if (ptr_info.size != .one or @typeInfo(ptr_info.child) != .array) @compileError(
                    "array ptr codec is not implemented for type " ++ @typeName(V),
                );
            }

            pub fn encode(
                writer: *std.Io.Writer,
                config: bk.Config,
                value: *const V,
                _: void,
            ) bk.EncodeWriterError!void {
                try length.codec.encode(writer, config, &value.*.len, {});
                try writer.writeAll(value.*);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: bk.Config,
                gpa_opt: ?std.mem.Allocator,
                value: *V,
                _: void,
            ) bk.DecodeReaderError!void {
                const gpa = gpa_opt.?;

                const expected_len = @typeInfo(ptr_info.child).array.len;
                const actual_len = try length.codec.decode(reader, null, config, null);
                if (actual_len != expected_len) return error.DecodeFailed;

                const result = (try gpa.alignedAlloc(
                    u8,
                    .fromByteUnits(ptr_info.alignment),
                    actual_len,
                ))[0..expected_len];

                try reader.readSliceAll(result);
                value.* = result;
            }

            pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V, _: void) void {
                const gpa = gpa_opt.?;
                gpa.free(value.*);
            }
        });

        /// Standard codec for an array pointer. Encodes the length.
        /// Also see `byte_array_ptr`.
        /// Decoding allocates the result.
        pub fn arrayPtr(element: StdCodec(Element)) StdCodecSelf {
            const EncodeCtx = element.codec.EncodeCtx;
            const DecodeCtx = element.codec.DecodeCtx;
            return .implement(EncodeCtx, DecodeCtx, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .one or @typeInfo(ptr_info.child) != .array) @compileError(
                        "array ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }

                const std_array: StdCodec(ptr_info.child) = .array(element);

                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const V,
                    ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    try length.codec.encode(writer, config, &value.*.len, ctx);
                    try std_array.codec.encode(writer, config, value.*, ctx);
                }

                pub const decodeInit = null;

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                    ctx: DecodeCtx,
                ) bk.DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const expected_len = @typeInfo(ptr_info.child).array.len;
                    const actual_len = try length.codec.decode(reader, null, config, null);
                    if (actual_len != expected_len) return error.DecodeFailed;

                    const array_ptr = (try gpa.alignedAlloc(
                        @typeInfo(ptr_info.child).array.child,
                        .fromByteUnits(ptr_info.alignment),
                        actual_len,
                    ))[0..expected_len];
                    errdefer gpa.free(array_ptr);

                    try std_array.codec.decodeInto(reader, gpa, config, array_ptr, ctx);
                    value.* = array_ptr;
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    std_array.codec.free(gpa, value.*, ctx);
                    gpa.free(value.*);
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
        pub fn arrayList(element: StdCodec(ArrayListElem)) StdCodecSelf {
            const alignment: std.mem.Alignment =
                .fromByteUnits(@typeInfo(V.Slice).pointer.alignment);
            const ArrayListType = std.ArrayListAlignedUnmanaged(ArrayListElem, alignment);
            const EncodeCtx = element.codec.EncodeCtx;
            const DecodeCtx = element.codec.DecodeCtx;
            return .implement(EncodeCtx, DecodeCtx, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const ArrayListType,
                    ctx: EncodeCtx,
                ) bk.EncodeWriterError!void {
                    const slice_codec: StdCodec(ArrayListType.Slice) = .slice(element);
                    try slice_codec.codec.encode(writer, config, &value.items, ctx);
                }

                pub fn decodeInit(
                    gpa_opt: ?std.mem.Allocator,
                    values: []ArrayListType,
                    _: DecodeCtx,
                ) std.mem.Allocator.Error!void {
                    _ = gpa_opt.?;
                    @memset(values, .empty);
                }

                pub fn decode(
                    reader: *std.Io.Reader,
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *ArrayListType,
                    ctx: DecodeCtx,
                ) bk.DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const len = try length.codec.decode(reader, null, config, null);
                    try value.ensureTotalCapacityPrecise(gpa, len);

                    if (len > value.items.len) {
                        const additional = value.addManyAsSliceAssumeCapacity(len - value.items.len);
                        element.codec.decodeInitMany(gpa, additional, ctx) catch |err| {
                            value.shrinkRetainingCapacity(len - additional.len);
                            return err;
                        };
                    } else if (len < value.items.len) {
                        for (value.items[len..]) |*elem| {
                            element.codec.free(gpa, elem, ctx);
                        }
                        value.shrinkRetainingCapacity(len);
                    }
                    std.debug.assert(value.items.len == len);

                    for (value.items) |*elem| {
                        try element.codec.decodeInto(reader, gpa, config, elem, ctx);
                    }
                }

                pub fn free(
                    gpa_opt: ?std.mem.Allocator,
                    value: *const ArrayListType,
                    ctx: DecodeCtx,
                ) void {
                    const gpa = gpa_opt.?;
                    if (element.codec.freeFn != null) {
                        for (value.items) |*elem| element.free(gpa, elem, ctx);
                    }
                    var copy = value.*;
                    copy.deinit(gpa);
                }
            });
        }

        const maybe_array_hm_info: ?ArrayHashMapInfo = .from(V);

        pub fn ArrayHashMapCtxs(
            std_key: StdCodec(if (maybe_array_hm_info) |hm_info| hm_info.K else void),
            std_val: StdCodec(if (maybe_array_hm_info) |hm_info| hm_info.V else void),
        ) type {
            return struct {
                pub const EncodeCtx = struct {
                    key: std_key.codec.EncodeCtx,
                    val: std_val.codec.EncodeCtx,
                };
                pub const DecodeCtx = struct {
                    key: std_key.codec.DecodeCtx,
                    val: std_val.codec.DecodeCtx,
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
        /// * `arrayHashMapCtxs`
        pub fn arrayHashMap(
            std_key: StdCodec(if (maybe_array_hm_info) |hm_info| hm_info.K else void),
            std_val: StdCodec(if (maybe_array_hm_info) |hm_info| hm_info.V else void),
        ) StdCodecSelf {
            const hm_info = comptime maybe_array_hm_info orelse @compileError(@typeName(V) ++ " is not an array hash map.");
            const Map = std.ArrayHashMapUnmanaged(
                hm_info.K,
                hm_info.V,
                hm_info.Context,
                hm_info.store_hash,
            );
            const Ctxs = ArrayHashMapCtxs(std_key, std_val);
            const EncodeCtx = Ctxs.EncodeCtx;
            const DecodeCtx = Ctxs.DecodeCtx;

            const encode_ctx_kind: FieldGroupKind = .max(
                .fromType(@FieldType(EncodeCtx, "key")),
                .fromType(@FieldType(EncodeCtx, "val")),
            );
            const EncodeCtxParam = switch (encode_ctx_kind) {
                .some_required => EncodeCtx,
                .all_opt_or_void => ?EncodeCtx,
                .all_void => void,
            };
            const decode_ctx_kind: FieldGroupKind = .max(
                .fromType(@FieldType(DecodeCtx, "key")),
                .fromType(@FieldType(DecodeCtx, "val")),
            );
            const DecodeCtxParam = switch (decode_ctx_kind) {
                .some_required => DecodeCtx,
                .all_opt_or_void => ?DecodeCtx,
                .all_void => void,
            };

            return .implement(EncodeCtxParam, DecodeCtxParam, struct {
                pub fn encode(
                    writer: *std.Io.Writer,
                    config: bk.Config,
                    value: *const Map,
                    maybe_ctx: EncodeCtxParam,
                ) bk.EncodeWriterError!void {
                    const key_ctx, const val_ctx = unwrapKeyValCtxs(.encode, maybe_ctx);

                    try length.codec.encode(writer, config, &value.count(), {});
                    for (value.keys(), value.values()) |*k, *v| {
                        try std_key.codec.encode(writer, config, k, key_ctx);
                        try std_val.codec.encode(writer, config, v, val_ctx);
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
                    config: bk.Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *Map,
                    maybe_ctx: DecodeCtxParam,
                ) bk.DecodeReaderError!void {
                    const gpa = gpa_opt.?;
                    const key_ctx, const val_ctx = unwrapKeyValCtxs(.decode, maybe_ctx);

                    const len = try length.codec.decode(reader, null, config, null);
                    try value.ensureTotalCapacity(gpa, len);

                    const original_count = value.count();
                    for (
                        value.keys()[0..@min(len, original_count)],
                        value.values()[0..@min(len, original_count)],
                    ) |*k, *v| {
                        try std_key.codec.decodeInto(reader, gpa, config, k, key_ctx);
                        try std_val.codec.decodeInto(reader, gpa, config, v, val_ctx);
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
                            std_key.codec.free(gpa, k, key_ctx);
                            std_val.codec.free(gpa, v, val_ctx);
                        }
                        value.shrinkRetainingCapacity(len);
                    } else if (len > original_count) for (original_count..len) |_| {
                        const k = try std_key.codec.decode(reader, gpa, config, key_ctx);
                        errdefer std_key.codec.free(gpa, &k, key_ctx);

                        const v = try std_val.codec.decode(reader, gpa, config, val_ctx);
                        errdefer std_val.codec.free(gpa, &v, val_ctx);

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
                    if (std_key.codec.freeFn == null and std_val.codec.freeFn == null) return;
                    const key_ctx, const val_ctx = unwrapKeyValCtxs(.decode, maybe_ctx);
                    for (value.keys(), value.values()) |*k, *v| {
                        std_key.codec.free(gpa, k, key_ctx);
                        std_val.codec.free(gpa, v, val_ctx);
                    }
                }

                fn unwrapKeyValCtxs(
                    comptime which: enum { encode, decode },
                    maybe_ctx: anytype,
                ) switch (which) {
                    .encode => struct { std_key.codec.EncodeCtx, std_val.codec.EncodeCtx },
                    .decode => struct { std_key.codec.DecodeCtx, std_val.codec.DecodeCtx },
                } {
                    const KeyCtx, const ValCtx = switch (which) {
                        .encode => .{ std_key.codec.EncodeCtx, std_val.codec.EncodeCtx },
                        .decode => .{ std_key.codec.DecodeCtx, std_val.codec.DecodeCtx },
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
            });
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
                    else => @compileError(@typeName(V) ++ " is not a valid indexable pointer."),
                },
                .slice => ptr_info.child,
                .many => ptr_info.child,
                else => @compileError(@typeName(V) ++ " is not a valid indexable pointer."),
            },
            else => @compileError(@typeName(V) ++ " is not an array, vector, or pointer."),
        };

        /// A struct with the same set of field names as `V` (a struct or a union), wherein each field
        /// has a type `StdCodec(@FieldType(V, field_name))`, where `field_name` is the corresponding name
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
                        const FieldCodec = StdCodec(v_field.type);
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
            else => @compileError(@typeName(V) ++ " is not a struct or a union"),
        };

        pub fn FieldContexts(field_codecs: Fields) struct {
            type,
            type,
            enum { need_decode_init, no_decode_init },
            enum { need_free, no_free },
        } {
            const fields, const is_tuple = switch (@typeInfo(V)) {
                .@"struct" => |s_info| .{ s_info.fields, s_info.is_tuple },
                .@"union" => |u_info| .{ u_info.fields, false },
                else => @compileError("doesn't apply for " ++ @typeName(V)),
            };

            var any_decode_init: bool = false;
            var any_free: bool = false;

            var enc_field_kind_max: FieldGroupKind = .all_void;
            var encode_fields: [fields.len]std.builtin.Type.StructField = undefined;

            var dec_field_kind_max: FieldGroupKind = .all_void;
            var decode_fields: [fields.len]std.builtin.Type.StructField = undefined;

            @setEvalBranchQuota(fields.len * 5 + 2);
            for (&encode_fields, &decode_fields, fields) |*encode_field, *decode_field, field| {
                const std_field: StdCodec(field.type) = @field(field_codecs, field.name);

                any_decode_init = any_decode_init or std_field.codec.decodeInitFn != null;
                any_free = any_free or std_field.codec.freeFn != null;

                const enc_field_kind: FieldGroupKind = .fromType(std_field.codec.EncodeCtx);
                enc_field_kind_max = .max(enc_field_kind_max, enc_field_kind);
                encode_field.* = .{
                    .name = field.name,
                    .type = std_field.codec.EncodeCtx,
                    .default_value_ptr = if (enc_field_kind == .all_void) @ptrCast(&{}) else null,
                    .is_comptime = false,
                    .alignment = @alignOf(std_field.codec.EncodeCtx),
                };

                const dec_field_kind: FieldGroupKind = .fromType(std_field.codec.DecodeCtx);
                dec_field_kind_max = .max(dec_field_kind_max, dec_field_kind);
                decode_field.* = .{
                    .name = field.name,
                    .type = std_field.codec.DecodeCtx,
                    .default_value_ptr = if (dec_field_kind == .all_void) @ptrCast(&{}) else null,
                    .is_comptime = false,
                    .alignment = @alignOf(std_field.codec.DecodeCtx),
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
            };
        }

        fn implement(
            comptime EncodeCtx: type,
            comptime DecodeCtx: type,
            comptime methods: type,
        ) StdCodecSelf {
            return .from(.implement(EncodeCtx, DecodeCtx, methods));
        }

        fn ImplementMethods(
            comptime EncodeCtx: type,
            comptime DecodeCtx: type,
            comptime methods: type,
        ) type {
            return Base.ImplementMethods(EncodeCtx, DecodeCtx, methods);
        }
    };
}

const FieldGroupKind = enum(u2) {
    /// All fields are void.
    all_void = 0,
    /// Some fields are not void, but are optional.
    all_opt_or_void = 1,
    /// Some fields are not void, and are also not optional.
    some_required = 2,

    fn fromType(comptime T: type) FieldGroupKind {
        return switch (@typeInfo(T)) {
            .void => .all_void,
            .optional => .all_opt_or_void,
            else => .some_required,
        };
    }

    fn max(a: FieldGroupKind, b: FieldGroupKind) FieldGroupKind {
        return @enumFromInt(@max(@intFromEnum(a), @intFromEnum(b)));
    }
};

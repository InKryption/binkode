const std = @import("std");

pub const varint = @import("varint.zig");
pub const StdInt = @import("stdint.zig").StdInt;

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

/// This represents an encoding & decoding scheme for a value of type `V`,
/// with behaviour defined by callbacks and an optional type-erased context.
///
/// NOTE: many methods in and adjacent to `Codec` are `inline` in order to propagate comptime-knowness.
pub fn Codec(comptime V: type) type {
    if (V == noreturn) unreachable;
    return struct {
        /// Pointer to any potentially runtime state needed to define the implementation's behaviour.
        ctx: ?*const anyopaque,
        /// VTable defining and describing the implementation's behaviour.
        vtable: *const VTable,
        const CodecSelf = @This();

        pub const VTable = struct {
            /// Encodes `value.*` to the `writer` stream in a manner defined by the implementation.
            encodeFn: *const fn (
                ctx: ?*const anyopaque,
                writer: *std.Io.Writer,
                config: Config,
                value: *const V,
            ) EncodeWriterError!void,

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
            decodeInitFn: ?*const fn (
                ctx: ?*const anyopaque,
                gpa_opt: ?std.mem.Allocator,
                /// Should be assumed to be undefined by the implementation, which should set
                /// it to a valid initial state for `decodeFn` to consume and decode into.
                values: []V,
            ) std.mem.Allocator.Error!void,

            /// Decodes into `value.*` from the `reader` stream.
            decodeFn: *const fn (
                ctx: ?*const anyopaque,
                reader: *std.Io.Reader,
                config: Config,
                gpa_opt: ?std.mem.Allocator,
                /// If `decodeInitFn == null`, expected to point to undefined data,
                /// which must be initialized.
                ///
                /// If `decodeInitFn != null`, expected to either have been initialized
                /// by `decodeInitFn`, or otherwise to be conformant with the documented
                /// expectations of the implementation.
                value: *V,
            ) DecodeReaderError!void,

            /// Frees any of the resources held by `value.*`.
            /// Assumes `value.*` is in a valid state as defined by the implementation,
            /// meaning it must be able to free any value produced by `decodeInitFn` and `decodeFn`.
            /// If this is null, the `free` method is a noop, meaning the implementation does not
            /// need to free any resources.
            freeFn: ?*const fn (
                ctx: ?*const anyopaque,
                gpa_opt: ?std.mem.Allocator,
                value: *const V,
            ) void,
        };

        /// Encodes `value.*` to the `writer` stream.
        pub inline fn encode(
            self: CodecSelf,
            writer: *std.Io.Writer,
            config: Config,
            value: *const V,
        ) EncodeWriterError!void {
            return self.vtable.encodeFn(self.ctx, writer, config, value);
        }

        /// Returns the number of bytes occupied by the encoded representation of `value.*`.
        pub inline fn encodedSize(
            self: CodecSelf,
            config: Config,
            value: *const V,
        ) EncodeError!u64 {
            var discarding: std.Io.Writer.Discarding = .init(&.{});
            const writer = &discarding.writer;
            self.encode(writer, config, value) catch |err| switch (err) {
                error.EncodeFailed => |e| return e,
                error.WriteFailed => unreachable, // discarding writer shouldn't fail here
            };
            return discarding.fullCount();
        }

        /// Encodes `value.*` to `slice`, returning the length of the encoded data in it.
        /// Returns `error.WriteFailed` if `slice` is not large enough to hold the full
        /// encoded representation of `value.*`, ie if `slice.len < self.encodedSize(config, value)`.
        pub inline fn encodeToSlice(
            self: CodecSelf,
            slice: []u8,
            config: Config,
            value: *const V,
        ) EncodeWriterError!usize {
            var fixed_writer: std.Io.Writer = .fixed(slice);
            try self.encode(&fixed_writer, config, value);
            return fixed_writer.end;
        }

        /// Encodes `value.*`, returning the encoded representation in the returned slice allocated with with `gpa`.
        /// Conveniently translates `error.WriteFailed` into `error.OutOfMemory`.
        pub inline fn encodeAlloc(
            self: CodecSelf,
            gpa: std.mem.Allocator,
            config: Config,
            value: *const V,
        ) (EncodeError || std.mem.Allocator.Error)![]u8 {
            var list: std.ArrayListUnmanaged(u8) = .empty;
            defer list.deinit(gpa);
            try self.encodeToArrayList(gpa, &list, config, value);
            return try list.toOwnedSlice(gpa);
        }

        /// Encodes `value.*`, appending the encoded representation to `list`, growing it with `gpa`.
        /// Conveniently translates `error.WriteFailed` into `error.OutOfMemory`.
        pub inline fn encodeToArrayList(
            self: CodecSelf,
            gpa: std.mem.Allocator,
            list: *std.ArrayListUnmanaged(u8),
            config: Config,
            value: *const V,
        ) (EncodeError || std.mem.Allocator.Error)!void {
            var allocating: std.Io.Writer.Allocating = .fromArrayList(gpa, list);
            defer list.* = allocating.toArrayList();
            const writer = &allocating.writer;
            self.encode(writer, config, value) catch |err| switch (err) {
                error.EncodeFailed => |e| return e,
                error.WriteFailed => return error.OutOfMemory, // the allocating writer's only failure is OOM
            };
        }

        /// Decodes the value from the `reader` stream and returns it.
        /// If the codec requires allocation, `gpa_opt` must be non-null.
        pub inline fn decode(
            self: CodecSelf,
            reader: *std.Io.Reader,
            config: Config,
            gpa_opt: ?std.mem.Allocator,
        ) DecodeReaderError!V {
            var value: V = undefined;
            try self.decodeInitOne(gpa_opt, &value);
            errdefer if (self.vtable.decodeInitFn != null) {
                self.free(gpa_opt, &value);
            };

            try self.decodeInto(reader, config, gpa_opt, &value);
            return value;
        }

        /// Same as `decode`, but takes a slice directly as input.
        /// Returns the value, and the number of bytes which were
        /// consumed to decode the value.
        pub inline fn decodeSlice(
            self: CodecSelf,
            src: []const u8,
            config: Config,
            gpa_opt: ?std.mem.Allocator,
        ) DecodeSliceError!struct { V, usize } {
            const decode_init_defined = self.vtable.decodeInitFn != null;

            var value: V = undefined;
            try self.decodeInitOne(gpa_opt, &value);
            errdefer if (decode_init_defined) self.free(gpa_opt, &value);

            const len = try self.decodeSliceInto(src, config, gpa_opt, &value);
            errdefer if (!decode_init_defined) self.free(gpa_opt, &value);

            std.debug.assert(len <= src.len);
            return .{ value, len };
        }

        /// Same as `decode`, but takes a slice directly as input.
        /// Returns `error.Overlong` if the number of bytes which were
        /// consumed to decode the value do not match `src.len`.
        pub inline fn decodeSliceExact(
            self: CodecSelf,
            src: []const u8,
            config: Config,
            gpa_opt: ?std.mem.Allocator,
        ) (DecodeSliceError || error{Overlong})!V {
            const value, const len = try self.decodeSlice(src, config, gpa_opt);
            if (len != src.len) return error.Overlong;
            return value;
        }

        /// Same as `decodeSliceExact`, but ignores `error.Overlong`.
        pub inline fn decodeSliceIgnoreLength(
            self: CodecSelf,
            src: []const u8,
            config: Config,
            gpa_opt: ?std.mem.Allocator,
        ) DecodeSliceError!V {
            const value, _ = try self.decodeSlice(src, config, gpa_opt);
            return value;
        }

        /// Same as `decodeInitMany`, but for a single value.
        pub inline fn decodeInitOne(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            value: *V,
        ) std.mem.Allocator.Error!void {
            try self.decodeInitMany(gpa_opt, @ptrCast(value));
        }

        /// See the `decodeInitFn` field in `VTable` for important commentary
        /// on the implications of this and related functions.
        /// This is mainly relevant to codec implementations consuming other codecs.
        /// If the codec requires allocation for decodeInit, `gpa_opt` must be non-null.
        pub inline fn decodeInitMany(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            value: []V,
        ) std.mem.Allocator.Error!void {
            const decodeInitFn = self.vtable.decodeInitFn orelse return;
            return try decodeInitFn(self.ctx, gpa_opt, value);
        }

        /// Decodes into `value.*` from the `reader` stream.
        /// If the codec requires allocation, `gpa_opt` must be non-null.
        /// Caller is responsible for freeing any resources held by `value.*`,
        /// including in event of failure.
        ///
        /// See doc comment on `decodeInitFn` for commentary on the expected
        /// initial state of `value.*`.
        pub inline fn decodeInto(
            self: CodecSelf,
            reader: *std.Io.Reader,
            config: Config,
            gpa_opt: ?std.mem.Allocator,
            value: *V,
        ) DecodeReaderError!void {
            return self.vtable.decodeFn(self.ctx, reader, config, gpa_opt, value);
        }

        /// Same as `decodeInto`, but takes a slice directly as input.
        /// Returns the number of bytes in `src` which were consumed to decode into `value.*`.
        pub inline fn decodeSliceInto(
            self: CodecSelf,
            src: []const u8,
            config: Config,
            gpa_opt: ?std.mem.Allocator,
            value: *V,
        ) DecodeSliceError!usize {
            var reader: std.Io.Reader = .fixed(src);
            self.decodeInto(&reader, config, gpa_opt, value) catch |err| switch (err) {
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
        pub inline fn free(
            self: CodecSelf,
            gpa_opt: ?std.mem.Allocator,
            value: *const V,
        ) void {
            const freeFn = self.vtable.freeFn orelse return;
            return freeFn(self.ctx, gpa_opt, value);
        }

        // -- Standard Codecs -- //

        /// Standard codec for a zero-sized value.
        /// Never fails to encode or decode.
        pub const std_void: CodecSelf = .implementNull(struct {
            comptime {
                if (@sizeOf(V) != 0) @compileError(
                    "void codec is not implemented for type " ++ @typeName(V) ++
                        " of size " ++ std.fmt.comptimePrint("{d}", .{@sizeOf(V)}),
                );
            }

            pub fn encode(writer: *std.Io.Writer, config: Config, value: *const V) EncodeWriterError!void {
                _ = writer;
                _ = config;
                _ = value;
            }

            pub const decodeInit = null;

            pub fn decode(reader: *std.Io.Reader, config: Config, gpa_opt: ?std.mem.Allocator, value: *V) DecodeReaderError!void {
                _ = reader;
                _ = config;
                _ = value;
                _ = gpa_opt;
            }

            pub const free = null;
        });

        /// Standard codec for a byte.
        /// Never fails to encode or decode.
        pub const std_byte: Codec(u8) = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, _: Config, value: *const u8) EncodeWriterError!void {
                try writer.writeByte(value.*);
            }

            pub const decodeInit = null;

            pub fn decode(reader: *std.Io.Reader, _: Config, _: ?std.mem.Allocator, value: *u8) DecodeReaderError!void {
                try reader.readSliceAll(value[0..1]);
            }

            pub const free = null;
        });

        /// Standard codec for a boolean.
        /// Never fails to encode.
        /// Failure to decode indicates a byte value other than 0 or 1.
        /// Decode's initial state is write-only.
        pub const std_bool: Codec(bool) = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, _: Config, value: *const bool) EncodeWriterError!void {
                try writer.writeByte(@intFromBool(value.*));
            }

            pub const decodeInit = null;

            pub fn decode(reader: *std.Io.Reader, _: Config, _: ?std.mem.Allocator, value: *bool) DecodeReaderError!void {
                value.* = switch (try reader.takeByte()) {
                    0 => false,
                    1 => true,
                    else => return error.DecodeFailed,
                };
            }

            pub const free = null;
        });

        /// Standard codec for an integer.
        /// Never fails to encode.
        /// Failure to decode indicates that the value overflowed.
        /// Decode's initial state is write-only.
        pub const std_int: CodecSelf = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, config: Config, value: *const V) EncodeWriterError!void {
                try StdInt(V).encode(writer, config, value.*);
            }

            pub const decodeInit = null;

            pub fn decode(reader: *std.Io.Reader, config: Config, _: ?std.mem.Allocator, value: *V) DecodeReaderError!void {
                value.* = try StdInt(V).decode(reader, config);
            }

            pub const free = null;
        });

        /// Standard codec for a float.
        /// Never fails to encode or decode.
        /// Decode's initial state is write-only.
        pub const std_float: CodecSelf = .implementNull(struct {
            const AsInt = std.meta.Int(.unsigned, @bitSizeOf(V));
            comptime {
                switch (V) {
                    f32, f64 => {},
                    else => @compileError("float codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(writer: *std.Io.Writer, config: Config, value: *const V) EncodeWriterError!void {
                const as_int_endian = std.mem.nativeTo(AsInt, @bitCast(value.*), config.endian);
                try writer.writeAll(@ptrCast(&as_int_endian));
            }

            pub const decodeInit = null;

            pub fn decode(reader: *std.Io.Reader, config: Config, _: ?std.mem.Allocator, value: *V) DecodeReaderError!void {
                try reader.readSliceAll(@ptrCast(value));
                value.* = @bitCast(std.mem.nativeTo(AsInt, @bitCast(value.*), config.endian));
            }

            pub const free = null;
        });

        /// Standard codec for a UTF-8 codepoint.
        /// Failure to encode indicates an invalid codepoint value.
        /// Failure to decode indicates an invalid codepoint value.
        /// Decode's initial state is write-only.
        pub const std_utf8_codepoint: CodecSelf = .implementNull(struct {
            comptime {
                switch (V) {
                    u1, u2, u3, u4, u5, u6, u7 => {},
                    u8, u16, u21, u32 => {},
                    else => @compileError("char codec is not implemented for " ++ @typeName(V)),
                }
            }

            pub fn encode(writer: *std.Io.Writer, _: Config, value: *const V) EncodeWriterError!void {
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

            pub fn decode(reader: *std.Io.Reader, _: Config, _: ?std.mem.Allocator, value: *V) DecodeReaderError!void {
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

        /// Standard codec for an optional.
        /// Allocation requirement defined by `payload_codec`.
        /// Never fails to encode the null bool, payload fallability is defined by `payload_codec`.
        /// Failure to decode indicates either a failure to decode the boolean, or the potential payload.
        /// When `payload_codec.decodeInitFn != null`, decode's initial state is null. If it is non-null,
        /// the existing payload must conform to `payload_codec`'s expectations; if the decoded value is
        /// null, the `payload_codec` will be used to free the existing payload.
        /// Otherwise, when `payload_codec.decodeInitFn == null`, decode's initial state is write-only.
        pub inline fn stdOptional(payload_codec: *const Codec(Child)) CodecSelf {
            const erased = ImplementCtxErasedMethods(Codec(Child), struct {
                const Unwrapped = @typeInfo(V).optional.child;

                pub fn encode(
                    pl_codec: Codec(Child),
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    std_bool.encode(writer, config, &(value.* != null)) catch |err| switch (err) {
                        error.WriteFailed => |e| return e,
                        error.EncodeFailed => unreachable, // bool never fails to encode
                    };
                    const payload = if (value.*) |*unwrapped| unwrapped else return;
                    try pl_codec.encode(writer, config, payload);
                }

                pub fn decodeInit(
                    pl_codec: Codec(Child),
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                ) std.mem.Allocator.Error!void {
                    _ = pl_codec;
                    _ = gpa_opt;
                    @memset(values, null);
                }

                pub fn decode(
                    pl_codec: Codec(Child),
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    const is_some = try std_bool.decode(reader, config, null);
                    if (is_some) {
                        if (pl_codec.vtable.decodeInitFn == null or value.* == null) {
                            value.* = @as(Unwrapped, undefined);
                            try pl_codec.decodeInitOne(gpa_opt, &value.*.?);
                        }
                        try pl_codec.decodeInto(reader, config, gpa_opt, &value.*.?);
                    } else {
                        if (pl_codec.vtable.decodeInitFn != null) if (value.*) |*pl| {
                            pl_codec.free(gpa_opt, pl);
                        };
                        value.* = null;
                    }
                }

                pub fn free(
                    pl_codec: Codec(Child),
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    const unwrapped = if (value.*) |*unwrapped| unwrapped else return;
                    pl_codec.free(gpa_opt, unwrapped);
                }
            });

            return .{
                .ctx = payload_codec,
                .vtable = &.{
                    .encodeFn = erased.encodeFn,
                    .decodeInitFn = if (payload_codec.vtable.decodeInitFn != null) erased.decodeInitFn else null,
                    .decodeFn = erased.decodeFn,
                    .freeFn = if (payload_codec.vtable.freeFn != null) erased.freeFn else null,
                },
            };
        }

        /// Standard codec for a struct.
        /// Allocation requirement defined by whether any codec in field codecs requires allocation.
        /// Failure to encode and decode defined by all of the field codecs in sequence.
        /// Decode's initial state is defined for each field based on the respective codec.
        pub inline fn stdStruct(field_codecs: *const Fields) CodecSelf {
            const s_fields = @typeInfo(V).@"struct".fields;

            const erased = ImplementCtxErasedMethods(Fields, struct {
                pub fn encode(
                    fields: Fields,
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    inline for (s_fields) |s_field| {
                        const field_codec: Codec(s_field.type) = @field(fields, s_field.name);
                        try field_codec.encode(writer, config, &@field(value, s_field.name));
                    }
                }

                pub fn decodeInit(
                    fields: Fields,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                ) std.mem.Allocator.Error!void {
                    for (values, 0..) |*value, value_i| {
                        errdefer for (values[0..value_i]) |*prev| {
                            freeFieldSubset(s_fields.len, fields, gpa_opt, prev);
                        };

                        inline for (s_fields, 0..) |s_field, s_field_i| {
                            errdefer freeFieldSubset(s_field_i, fields, gpa_opt, value);
                            const field_codec: Codec(s_field.type) = @field(fields, s_field.name);
                            const field_ptr = &@field(value, s_field.name);
                            try field_codec.decodeInitOne(gpa_opt, field_ptr);
                        }
                    }
                }

                pub fn decode(
                    fields: Fields,
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    inline for (s_fields, 0..) |s_field, i| {
                        errdefer freeFieldSubset(i, fields, gpa_opt, value);
                        const field_codec: Codec(s_field.type) = @field(fields, s_field.name);
                        const field_ptr = &@field(value, s_field.name);
                        try field_codec.decodeInto(reader, config, gpa_opt, field_ptr);
                    }
                }

                pub fn free(
                    fields: Fields,
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    freeFieldSubset(s_fields.len, fields, gpa_opt, value);
                }

                fn freeFieldSubset(
                    comptime n_fields_to_deinit: usize,
                    fields: Fields,
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    inline for (s_fields[0..n_fields_to_deinit]) |s_field| {
                        const field_codec: Codec(s_field.type) = @field(fields, s_field.name);
                        field_codec.free(gpa_opt, &@field(value, s_field.name));
                    }
                }
            });

            const any_decode_init = blk: {
                @setEvalBranchQuota(s_fields.len);
                inline for (s_fields) |s_field| {
                    const field_codec: Codec(s_field.type) = @field(field_codecs, s_field.name);
                    if (field_codec.vtable.decodeInitFn != null) break :blk true;
                } else break :blk false;
            };

            const any_free = blk: {
                @setEvalBranchQuota(s_fields.len);
                inline for (s_fields) |s_field| {
                    const field_codec: Codec(s_field.type) = @field(field_codecs, s_field.name);
                    if (field_codec.vtable.freeFn != null) break :blk true;
                } else break :blk false;
            };

            return .{
                .ctx = field_codecs,
                .vtable = &.{
                    .encodeFn = erased.encodeFn,
                    .decodeInitFn = if (any_decode_init) erased.decodeInitFn else null,
                    .decodeFn = erased.decodeFn,
                    .freeFn = if (any_free) erased.freeFn else null,
                },
            };
        }

        /// Standard codec for a tagged union, aka "enums" in the
        /// bincode specification, written in the context of rust.
        /// Allocation requirement defined by whether any codec in payload codecs requires allocation.
        /// Also see: `std_discriminant`.
        pub inline fn stdUnion(payload_codecs: *const Fields) CodecSelf {
            const union_info = @typeInfo(V).@"union";

            const erased = ImplementCtxErasedMethods(Fields, struct {
                const tag_codec: Codec(union_info.tag_type.?) = .std_discriminant;

                pub fn encode(
                    pl_codecs: Fields,
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    const tag: union_info.tag_type.? = value.*;
                    try tag_codec.encode(writer, config, &tag);
                    switch (value.*) {
                        inline else => |*payload, itag| {
                            const Payload = @TypeOf(payload.*);
                            const field_codec: Codec(Payload) = @field(pl_codecs, @tagName(itag));
                            try field_codec.encode(writer, config, payload);
                        },
                    }
                }

                pub const decodeInit = null;

                pub fn decode(
                    pl_codecs: Fields,
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    switch (try tag_codec.decode(reader, config, null)) {
                        inline else => |itag| {
                            value.* = @unionInit(V, @tagName(itag), undefined);
                            const Payload = @FieldType(V, @tagName(itag));
                            const payload_codec: Codec(Payload) = @field(pl_codecs, @tagName(itag));
                            const payload_ptr = &@field(value, @tagName(itag));
                            try payload_codec.decodeInitOne(gpa_opt, payload_ptr);
                            try payload_codec.decodeInto(reader, config, gpa_opt, payload_ptr);
                        },
                    }
                }

                pub fn free(
                    pl_codecs: Fields,
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    switch (value.*) {
                        inline else => |*payload, itag| {
                            const Payload = @TypeOf(payload.*);
                            const field_codec: Codec(Payload) = @field(pl_codecs, @tagName(itag));
                            field_codec.free(gpa_opt, payload);
                        },
                    }
                }
            });

            const any_free = blk: {
                @setEvalBranchQuota(union_info.fields.len);
                inline for (union_info.fields) |u_field| {
                    const payload_codec: Codec(u_field.type) = @field(payload_codecs, u_field.name);
                    if (payload_codec.vtable.freeFn != null) break :blk true;
                } else break :blk false;
            };

            return .{
                .ctx = payload_codecs,
                .vtable = &.{
                    .encodeFn = erased.encodeFn,
                    .decodeInitFn = null,
                    .decodeFn = erased.decodeFn,
                    .freeFn = if (any_free) erased.freeFn else null,
                },
            };
        }

        /// Standard codec for an enum used as a discriminant,
        /// aka the tag of a tagged union, aka the tag of a rust enum.
        /// Failure to decode indicates the value overflowed or didn't match a valid value.
        /// Decode's initial state is write-only.
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

            pub fn encode(writer: *std.Io.Writer, config: Config, value: *const V) EncodeWriterError!void {
                const as_u32: u32 = @intFromEnum(value.*);
                return Codec(u32).std_int.encode(writer, config, &as_u32);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                _: ?std.mem.Allocator,
                value: *V,
            ) DecodeReaderError!void {
                const as_u32 = try Codec(u32).std_int.decode(reader, config, null);
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

            pub const free = null;
        });

        /// Standard codec for a byte array. Encodes no length.
        /// Optimization over `stdArray(&.std_byte)`.
        /// Decode's initial state is write-only.
        pub const std_byte_array: CodecSelf = .implementNull(struct {
            pub fn encode(writer: *std.Io.Writer, _: Config, value: *const V) EncodeWriterError!void {
                try writer.writeAll(value);
            }

            pub const decodeInit = null;

            pub fn decode(
                reader: *std.Io.Reader,
                _: Config,
                _: ?std.mem.Allocator,
                value: *V,
            ) DecodeReaderError!void {
                try reader.readSliceAll(value);
            }

            pub const free = null;
        });

        /// Standard codec for an array. Encodes no length.
        /// Allocation requirement defined by element codec.
        /// Decode's initial state is defined as an array of initial states conforming to `element_codec`'s expectations.
        /// Also see `std_byte_array`.
        pub inline fn stdArray(element_codec: *const Codec(Element)) CodecSelf {
            const erased = ImplementCtxErasedMethods(Codec(Element), struct {
                const not_implemented_err_msg = "array codec not is not implemented for type " ++ @typeName(V);

                pub fn encode(
                    elem_codec: Codec(Element),
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| try elem_codec.encode(writer, config, elem),
                        .vector => |vec_info| for (0..vec_info.len) |i| try elem_codec.encode(writer, config, &value[i]),
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn decodeInit(
                    elem_codec: Codec(Element),
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                ) std.mem.Allocator.Error!void {
                    switch (@typeInfo(V)) {
                        .array => try elem_codec.decodeInitMany(gpa_opt, @ptrCast(values)), // flatten `[][n]E` as `[]E`.
                        .vector => |vec_info| for (values) |*value| {
                            var arr: [vec_info.len]Element = value.*;
                            try element_codec.decodeInitMany(gpa_opt, &arr);
                            value.* = arr;
                        },
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn decode(
                    elem_codec: Codec(Element),
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| try elem_codec.decodeInto(reader, config, gpa_opt, elem),
                        .vector => |vec_info| for (0..vec_info.len) |i| try elem_codec.decodeInto(reader, config, gpa_opt, &value[i]),
                        else => @compileError(not_implemented_err_msg),
                    }
                }

                pub fn free(
                    elem_codec: Codec(Element),
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    if (elem_codec.vtable.freeFn == null) return;
                    switch (@typeInfo(V)) {
                        .array => for (value) |*elem| elem_codec.free(gpa_opt, elem),
                        .vector => |vec_info| for (0..vec_info.len) |i| elem_codec.free(gpa_opt, &value[i]),
                        else => @compileError(not_implemented_err_msg),
                    }
                }
            });

            return .{
                .ctx = element_codec,
                .vtable = &.{
                    .encodeFn = erased.encodeFn,
                    .decodeInitFn = if (element_codec.vtable.decodeInitFn != null) erased.decodeInitFn else null,
                    .decodeFn = erased.decodeFn,
                    .freeFn = if (element_codec.vtable.freeFn != null) erased.freeFn else null,
                },
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
        pub const std_byte_slice: CodecSelf = .implementNull(struct {
            const ptr_info = @typeInfo(V).pointer;
            comptime {
                if (ptr_info.size != .slice) @compileError(
                    "single item ptr codec is not implemented for type " ++ @typeName(V),
                );
            }

            pub fn encode(writer: *std.Io.Writer, config: Config, value: *const V) EncodeWriterError!void {
                try Codec(usize).std_int.encode(writer, config, &value.len);
                try writer.writeAll(value.*);
            }

            pub fn decodeInit(gpa_opt: ?std.mem.Allocator, values: []V) std.mem.Allocator.Error!void {
                _ = gpa_opt.?;
                @memset(values, &.{});
            }

            pub fn decode(
                reader: *std.Io.Reader,
                config: Config,
                gpa_opt: ?std.mem.Allocator,
                value: *V,
            ) DecodeReaderError!void {
                const gpa = gpa_opt.?;

                const len = try Codec(usize).std_int.decode(reader, config, null);
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

            pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V) void {
                const gpa = gpa_opt.?;
                gpa.free(value.*);
            }
        });

        /// Standard codec for a slice. Encodes the length.
        /// Requires allocation, for the slice, and possibly for the elements (based on element codec).
        /// Also see `std_byte_array`.
        pub inline fn stdSlice(element_codec: *const Codec(Element)) CodecSelf {
            return .implementCtx(element_codec, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .slice) @compileError(
                        "single item ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }

                pub fn encode(
                    elem_codec: Codec(Element),
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    try Codec(usize).std_int.encode(writer, config, &value.len);
                    for (value.*) |*elem| try elem_codec.encode(writer, config, elem);
                }

                pub const decodeInit = null;

                pub fn decode(
                    elem_codec: Codec(Element),
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const len = try Codec(usize).std_int.decode(reader, config, null);
                    const slice = try gpa.alignedAlloc(ptr_info.child, .fromByteUnits(ptr_info.alignment), len);
                    errdefer gpa.free(slice);

                    for (slice, 0..) |*elem, i| {
                        errdefer if (elem_codec.vtable.freeFn != null) {
                            for (slice[0..i]) |*prev| elem_codec.free(gpa, prev);
                        };
                        try elem_codec.decodeInto(reader, config, gpa, elem);
                    }
                    value.* = slice;
                }

                pub fn free(
                    elem_codec: Codec(Element),
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    const gpa = gpa_opt.?;
                    if (elem_codec.vtable.freeFn != null) {
                        for (value.*) |*elem| elem_codec.free(gpa, elem);
                    }
                    gpa.free(value.*);
                }
            });
        }

        /// Standard codec for a byte array pointer. Encodes the length. Optimization over `stdArrayPtr(&.std_byte)`.
        /// Requires allocation.
        pub const std_byte_array_ptr: CodecSelf = .implementNull(struct {
            const ptr_info = @typeInfo(V).pointer;
            comptime {
                if (ptr_info.size != .one or @typeInfo(ptr_info.child) != .array) @compileError(
                    "array ptr codec is not implemented for type " ++ @typeName(V),
                );
            }

            pub fn encode(writer: *std.Io.Writer, config: Config, value: *const V) EncodeWriterError!void {
                try Codec(usize).std_int.encode(writer, config, &value.*.len);
                try writer.writeAll(value.*);
            }

            pub const decodeInit = null;

            pub fn decode(reader: *std.Io.Reader, config: Config, gpa_opt: ?std.mem.Allocator, value: *V) DecodeReaderError!void {
                const gpa = gpa_opt.?;

                const expected_len = @typeInfo(ptr_info.child).array.len;
                const actual_len = try Codec(usize).std_int.decode(reader, config, null);
                if (actual_len != expected_len) return error.DecodeFailed;

                const slice = (try gpa.alignedAlloc(
                    u8,
                    .fromByteUnits(ptr_info.alignment),
                    actual_len,
                ))[0..expected_len];

                try reader.readSliceAll(slice);
                value.* = slice;
            }

            pub fn free(gpa_opt: ?std.mem.Allocator, value: *const V) void {
                const gpa = gpa_opt.?;
                gpa.free(value.*);
            }
        });

        /// Standard codec for an array pointer. Encodes the length.
        /// Also see `std_byte_array_ptr`.
        /// Decoding allocates the result.
        pub inline fn stdArrayPtr(element_codec: *const Codec(Element)) CodecSelf {
            return .implementCtx(element_codec, struct {
                const ptr_info = @typeInfo(V).pointer;
                comptime {
                    if (ptr_info.size != .one or @typeInfo(ptr_info.child) != .array) @compileError(
                        "array ptr codec is not implemented for type " ++ @typeName(V),
                    );
                }

                pub fn encode(
                    elem_codec: Codec(Element),
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    try Codec(usize).std_int.encode(writer, config, &value.*.len);
                    try Codec(ptr_info.child).stdArray(&elem_codec).encode(writer, config, value.*);
                }

                pub const decodeInit = null;

                pub fn decode(
                    elem_codec: Codec(Element),
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    const gpa = gpa_opt.?;

                    const expected_len = @typeInfo(ptr_info.child).array.len;
                    const actual_len = try Codec(usize).std_int.decode(reader, config, null);
                    if (actual_len != expected_len) return error.DecodeFailed;

                    const slice = (try gpa.alignedAlloc(
                        @typeInfo(ptr_info.child).array.child,
                        .fromByteUnits(ptr_info.alignment),
                        actual_len,
                    ))[0..expected_len];
                    errdefer gpa.free(slice);

                    try Codec(ptr_info.child).stdArray(&elem_codec).decodeInto(reader, config, gpa, slice);
                    value.* = slice;
                }

                pub fn free(
                    elem_codec: Codec(Element),
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    const gpa = gpa_opt.?;
                    Codec(ptr_info.child).stdArray(&elem_codec).free(gpa, value.*);
                    gpa.free(value.*);
                }
            });
        }

        /// Standard codec for a single item pointer.
        /// Decoding allocates the result.
        /// Disallows `Child = [n]T` and `Child = @Vector(n, T)`, see `stdArrayPtr` instead.
        pub inline fn stdSingleItemPtr(ptr_child_codec: *const Codec(Child)) CodecSelf {
            return .implementCtx(ptr_child_codec, struct {
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
                    child_codec: Codec(Child),
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    try child_codec.encode(writer, config, value.*);
                }

                pub const decodeInit = null;

                pub fn decode(
                    child_codec: Codec(Child),
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
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
                    try child_codec.decodeInto(reader, config, gpa, ptr);
                    value.* = ptr;
                }

                pub fn free(
                    child_codec: Codec(Child),
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    const gpa = gpa_opt.?;
                    child_codec.free(gpa, value.*);
                    gpa.destroy(value.*);
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

        // -- Helpers for safely implementing common codecs -- //

        pub inline fn implementCtx(
            ctx_ptr: anytype,
            comptime methods: type,
        ) CodecSelf {
            const erased = ImplementCtxErasedMethods(@TypeOf(ctx_ptr.*), methods);

            return .{
                .ctx = @ptrCast(ctx_ptr),
                .vtable = comptime &.{
                    .encodeFn = erased.encodeFn,
                    .decodeInitFn = if (@TypeOf(methods.decodeInit) != @TypeOf(null)) erased.decodeInitFn else null,
                    .decodeFn = erased.decodeFn,
                    .freeFn = if (@TypeOf(methods.free) != @TypeOf(null)) erased.freeFn else null,
                },
            };
        }

        fn ImplementCtxErasedMethods(
            comptime Ctx: type,
            comptime methods: type,
        ) type {
            return struct {
                fn encodeFn(
                    ctx: ?*const anyopaque,
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    const casted: *const Ctx = @ptrCast(@alignCast(ctx.?));
                    try methods.encode(casted.*, writer, config, value);
                }

                fn decodeInitFn(
                    ctx: ?*const anyopaque,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                ) std.mem.Allocator.Error!void {
                    const casted: *const Ctx = @ptrCast(@alignCast(ctx.?));
                    try methods.decodeInit(casted.*, gpa_opt, values);
                }

                fn decodeFn(
                    ctx: ?*const anyopaque,
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    const casted: *const Ctx = @ptrCast(@alignCast(ctx.?));
                    try methods.decode(casted.*, reader, config, gpa_opt, value);
                }

                fn freeFn(
                    ctx: ?*const anyopaque,
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    const casted: *const Ctx = @ptrCast(@alignCast(ctx.?));
                    methods.free(casted.*, gpa_opt, value);
                }
            };
        }

        /// Expects `methods` to be a namespace with the following methods defined:
        /// ```zig
        /// fn encode(writer: *std.Io.Writer, config: Config, value: *const V) EncodeWriterError!void { ... }
        /// fn decode(reader: *std.Io.Reader, config: Config, value: *V) DecodeReaderError!void { ... }
        /// ```
        pub inline fn implementNull(comptime methods: type) CodecSelf {
            const erased = ImplementNullErasedMethods(methods);
            return .{
                .ctx = null,
                .vtable = comptime &.{
                    .encodeFn = erased.encodeFn,
                    .decodeInitFn = if (@TypeOf(methods.decodeInit) != @TypeOf(null)) erased.decodeInitFn else null,
                    .decodeFn = erased.decodeFn,
                    .freeFn = if (@TypeOf(methods.free) != @TypeOf(null)) erased.freeFn else null,
                },
            };
        }

        fn ImplementNullErasedMethods(comptime methods: type) type {
            return struct {
                fn encodeFn(
                    ctx: ?*const anyopaque,
                    writer: *std.Io.Writer,
                    config: Config,
                    value: *const V,
                ) EncodeWriterError!void {
                    if (ctx != null) unreachable;
                    try methods.encode(writer, config, value);
                }

                fn decodeInitFn(
                    ctx: ?*const anyopaque,
                    gpa_opt: ?std.mem.Allocator,
                    values: []V,
                ) std.mem.Allocator.Error!void {
                    if (ctx != null) unreachable;
                    try methods.decodeInit(gpa_opt, values);
                }

                fn decodeFn(
                    ctx: ?*const anyopaque,
                    reader: *std.Io.Reader,
                    config: Config,
                    gpa_opt: ?std.mem.Allocator,
                    value: *V,
                ) DecodeReaderError!void {
                    if (ctx != null) unreachable;
                    try methods.decode(reader, config, gpa_opt, value);
                }

                fn freeFn(
                    ctx: ?*const anyopaque,
                    gpa_opt: ?std.mem.Allocator,
                    value: *const V,
                ) void {
                    if (ctx != null) unreachable;
                    methods.free(gpa_opt, value);
                }
            };
        }
    };
}

test "std_void" {
    var null_reader: std.Io.Reader = .failing;
    var null_writer: std.Io.Writer.Discarding = .init(&.{});
    const void_codec: Codec(void) = .std_void;
    try std.testing.expectEqual({}, void_codec.encode(&null_writer.writer, .default, &{}));
    try std.testing.expectEqual({}, void_codec.decode(&null_reader, .default, null));
    try std.testing.expectEqual(0, void_codec.encodedSize(.default, &{}));
}

test "std_byte" {
    const byte_codec: Codec(u8) = .std_byte;
    try std.testing.expectEqual('f', byte_codec.decodeSliceExact(&.{'f'}, .default, null));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, .default, null));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, .default, null));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeSliceExact(&.{}, .default, null));
    try std.testing.expectError(error.Overlong, byte_codec.decodeSliceExact("bar", .default, null));
    try std.testing.expectEqual(1, byte_codec.encodedSize(.default, &'z'));
}

test "std_bool" {
    const bool_codec: Codec(bool) = .std_bool;
    try std.testing.expectEqual(false, bool_codec.decodeSliceExact(&.{0}, .default, null));
    try std.testing.expectEqual(true, bool_codec.decodeSliceExact(&.{1}, .default, null));
    try std.testing.expectError(error.DecodeFailed, bool_codec.decodeSliceExact(&.{2}, .default, null));
    try std.testing.expectError(error.EndOfStream, bool_codec.decodeSliceExact(&.{}, .default, null));
    try std.testing.expectError(error.Overlong, bool_codec.decodeSliceExact(&.{ 1, 0 }, .default, null));
    try std.testing.expectEqual(1, bool_codec.encodedSize(.default, &false));
    try std.testing.expectEqual(1, bool_codec.encodedSize(.default, &true));
}

test "std_int" {
    const u32_codec: Codec(u32) = .std_int;
    const config: Config = .{ .endian = .little, .int = .varint };

    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, 250, &.{250});
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, 251, &.{ 251, 251, 0 });
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, 300, &.{ 251, 0x2C, 1 });
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, std.math.maxInt(u16), &.{ 251, 0xFF, 0xFF });
    try testEncodedBytesAndRoundTrip(u32, u32_codec, config, std.math.maxInt(u16) + 1, &.{ 252, 0, 0, 1, 0 });

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
    try std.testing.expectEqual(1, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{7F}'));
    try std.testing.expectEqual(2, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{ff}'));
    try std.testing.expectEqual(3, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{fff}'));
    try std.testing.expectEqual(4, Codec(u32).std_utf8_codepoint.encodedSize(.default, &'\u{fffff}'));
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

    const codec: Codec(?u32) = .stdOptional(&.std_int);
    const config: Config = .{ .endian = .little, .int = .varint };
    try testEncodedBytesAndRoundTrip(?u32, codec, config, 3, "\x01" ++ "\x03");
    try testEncodedBytesAndRoundTrip(?u32, codec, config, null, "\x00");
    try testEncodedBytesAndRoundTrip(?u32, codec, config, 251, "\x01" ++ "\xFB\xFB\x00");
}

test "stdStruct" {
    const S = struct {
        a: u32,
        b: f64,

        const bk_codec: Codec(@This()) = .stdStruct(&.{
            .a = .std_int,
            .b = .std_float,
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
    try testCodecRoundTrips(S, S.bk_codec, &struct_test_edge_cases);

    try testEncodedBytesAndRoundTrip(
        S,
        S.bk_codec,
        .{ .endian = .little, .int = .varint },
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

        const bk_codec: Codec(@This()) = .stdUnion(&.{
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
    };

    try testCodecRoundTrips(U, U.bk_codec, &.{
        .void,
        .{ .char = 42 },
        .{ .int = 1111111111 },
        .{ .float = -7 },
        .{ .record = .{ .a = 1, .b = 2, .c = .foo } },
    });
}

test "std_byte_array" {
    try testCodecRoundTrips([3]u8, .std_byte_array, &.{ "foo".*, "bar".*, "baz".* });
}

test "stdArray" {
    try testCodecRoundTrips([2]u64, .stdArray(&.std_int), @ptrCast(&intTestEdgeCases(u64) ++ intTestEdgeCases(u64)));
    try testCodecRoundTrips([2]u64, .stdArray(&.std_int), &.{
        .{ 1, 2 },
        .{ 61, 313131 },
        @splat(111111111),
    });

    try testCodecRoundTrips([2]f32, .stdArray(&.std_float), @ptrCast(&floatTestEdgeCases(f32) ++ floatTestEdgeCases(f32)));
    try testCodecRoundTrips([2]f64, .stdArray(&.std_float), @ptrCast(&floatTestEdgeCases(f64) ++ floatTestEdgeCases(f64)));
    try testCodecRoundTrips(@Vector(2, f32), .stdArray(&.std_float), &.{
        .{ -1.0, 2 },
        .{ 61, -313131 },
        @splat(111111111.0),
    });
}

test "std_byte_slice" {
    try testCodecRoundTrips([]const u8, .std_byte_slice, &.{
        &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 }, "foo",  "bar",  "baz",
        &.{ 127, std.math.maxInt(u8) },  "fizz", "buzz", "fizzbuzz",
    });
}

test "stdSlice" {
    try testCodecRoundTrips([]const u32, .stdSlice(&.std_int), &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5, 6 },
        &.{ 7, 8, 9, 10, 11 },
        &.{ 12, 13, 14, 15, 16, 17 },
        &.{ 18, 19, 20, 21, 22, 23, 24 },
        &.{ 25, 26, 27, 28, 29, 30, 31, 32 },
    });
}

test "std_byte_array_ptr" {
    try testCodecRoundTrips(*const [3]u8, .std_byte_array_ptr, &.{
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
    try testCodecRoundTrips(*const [3]u32, .stdArrayPtr(&.std_int), &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5 },
        &.{ 7, 8, 9 },
        &.{ 12, 13, 14 },
        &.{ 18, 19, 20 },
        &.{ 25, 26, 27 },
    });
}

test "stdSingleItemPtr" {
    try testCodecRoundTrips(*const u32, .stdSingleItemPtr(&.std_int), &.{
        &0, &1, &2, &10000, &std.math.maxInt(u32),
    });
}

test "decodeSliceIgnoreLength" {
    const config: Config = .{ .endian = .little, .int = .varint };
    const overlong_varint_src = [_]u8{ 250, 1 };
    try std.testing.expectEqual(
        250,
        Codec(u32).std_int.decodeSliceExact((&overlong_varint_src)[0..1], config, null),
    );
    try std.testing.expectError(
        error.Overlong,
        Codec(u32).std_int.decodeSliceExact(&overlong_varint_src, config, null),
    );
    try std.testing.expectEqual(
        250,
        Codec(u32).std_int.decodeSliceIgnoreLength(&overlong_varint_src, config, null),
    );
}

test "optional slice memory re-use" {
    const gpa = std.testing.allocator;

    const codec: Codec(?[]const u8) = .stdOptional(&.std_byte_slice);

    const expected: ?[]const u8 = "foo";
    const expected_encoded_bytes = try codec.encodeAlloc(gpa, .default, &expected);
    defer gpa.free(expected_encoded_bytes);

    var actual: ?[]const u8 = try gpa.alloc(u8, 100);
    defer if (actual) |res| gpa.free(res);
    try std.testing.expectEqual(
        expected_encoded_bytes.len,
        codec.decodeSliceInto(expected_encoded_bytes, .default, gpa, &actual),
    );
    try std.testing.expectEqualDeep(expected, actual);
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
    value: T,
    expected: []const u8,
) !void {
    const actual_bytes = try codec.encodeAlloc(std.testing.allocator, config, &value);
    defer std.testing.allocator.free(actual_bytes);
    try std.testing.expectEqualSlices(u8, expected, actual_bytes);

    const actual_value = codec.decodeSliceExact(actual_bytes, config, std.testing.allocator);
    defer if (actual_value) |*unwrapped| codec.free(std.testing.allocator, unwrapped) else |_| {};
    try std.testing.expectEqualDeep(value, actual_value);
}

fn testCodecRoundTrips(
    comptime T: type,
    codec: Codec(T),
    values: []const T,
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
            for (values) |int| try codec.encode(encoded_writer, config, &int);
        }

        var encoded_reader: std.Io.Reader = .fixed(buffer.items);
        for (values, 0..) |expected, i| {
            const actual = codec.decode(
                &encoded_reader,
                config,
                std.testing.allocator,
            );
            defer if (actual) |*unwrapped| {
                codec.free(std.testing.allocator, unwrapped);
            } else |_| {};
            errdefer std.log.err("[{d}]: expected '{any}', actual: '{any}'", .{ i, expected, actual });
            try std.testing.expectEqualDeep(expected, actual);
        }
        try std.testing.expectEqual(0, encoded_reader.bufferedLen());
    }
}

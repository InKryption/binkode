const std = @import("std");

const utils = @import("utils.zig");
const ArrayHashMapInfo = utils.ArrayHashMapInfo;

pub const varint = @import("varint.zig");
pub const StdCodec = @import("std_codec.zig").StdCodec;

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
        pub fn standard(std_codec: StdCodec(V)) CodecSelf {
            return std_codec.codec;
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

test "standard void" {
    var null_reader: std.Io.Reader = .failing;
    var null_writer: std.Io.Writer.Discarding = .init(&.{});
    const void_codec: Codec(void) = .standard(.empty);
    try std.testing.expectEqual({}, void_codec.encode(&null_writer.writer, .default, &{}, {}));
    try std.testing.expectEqual({}, void_codec.decode(&null_reader, null, .default, {}));
    try std.testing.expectEqual(0, void_codec.encodedSize(.default, &{}, {}));
}

test "standard byte" {
    const byte_codec: Codec(u8) = .standard(.byte);
    try std.testing.expectEqual('f', byte_codec.decodeSliceExact(&.{'f'}, null, .default, {}));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, null, .default, {}));
    try std.testing.expectEqual('o', byte_codec.decodeSliceExact(&.{'o'}, null, .default, {}));
    try std.testing.expectError(error.EndOfStream, byte_codec.decodeSliceExact(&.{}, null, .default, {}));
    try std.testing.expectError(error.Overlong, byte_codec.decodeSliceExact("bar", null, .default, {}));
    try std.testing.expectEqual(1, byte_codec.encodedSize(.default, &'z', {}));
}

test "standard bool" {
    const bool_codec: Codec(bool) = .standard(.boolean);
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

test "standard int" {
    try testEncodedBytesAndRoundTrip(u32, .standard(.int), .{
        .config = .cfg(.little, .varint),
        .enc_ctx = {},
        .dec_ctx = null,
        .original = 250,
        .expected_bytes = &.{250},
    });
    try testEncodedBytesAndRoundTrip(u32, .standard(.int), .{
        .config = .cfg(.little, .varint),
        .enc_ctx = {},
        .dec_ctx = null,
        .original = 251,
        .expected_bytes = &.{ 251, 251, 0 },
    });
    try testEncodedBytesAndRoundTrip(u32, .standard(.int), .{
        .config = .cfg(.little, .varint),
        .enc_ctx = {},
        .dec_ctx = null,
        .original = 300,
        .expected_bytes = &.{ 251, 0x2C, 1 },
    });
    try testEncodedBytesAndRoundTrip(u32, .standard(.int), .{
        .config = .cfg(.little, .varint),
        .enc_ctx = {},
        .dec_ctx = null,
        .original = std.math.maxInt(u16),
        .expected_bytes = &.{ 251, 0xFF, 0xFF },
    });
    try testEncodedBytesAndRoundTrip(u32, .standard(.int), .{
        .config = .cfg(.little, .varint),
        .enc_ctx = {},
        .dec_ctx = null,
        .original = std.math.maxInt(u16) + 1,
        .expected_bytes = &.{ 252, 0, 0, 1, 0 },
    });

    try testCodecRoundTrips(i16, .standard(.int), {}, null, &intTestEdgeCases(i16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(u16, .standard(.int), {}, null, &intTestEdgeCases(u16) ++ .{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(i32, .standard(.int), {}, null, &intTestEdgeCases(i32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u32, .standard(.int), {}, null, &intTestEdgeCases(u32) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i64, .standard(.int), {}, null, &intTestEdgeCases(i64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u64, .standard(.int), {}, null, &intTestEdgeCases(u64) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i128, .standard(.int), {}, null, &intTestEdgeCases(i128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u128, .standard(.int), {}, null, &intTestEdgeCases(u128) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(i256, .standard(.int), {}, null, &intTestEdgeCases(i256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(u256, .standard(.int), {}, null, &intTestEdgeCases(u256) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(isize, .standard(.int), {}, null, &intTestEdgeCases(isize) ++ .{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(usize, .standard(.int), {}, null, &intTestEdgeCases(usize) ++ .{ 1, 5, 1000000000, 32, 8 });
}

test "standard float" {
    try testCodecRoundTrips(f32, .standard(.float), {}, {}, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f32, .standard(.float), {}, {}, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f64, .standard(.float), {}, {}, &.{ 1, 5, 10000, 32, 8 });
    try testCodecRoundTrips(f64, .standard(.float), {}, {}, &.{ 1, 5, 1000000000, 32, 8 });
    try testCodecRoundTrips(f32, .standard(.float), {}, {}, &floatTestEdgeCases(f32));
    try testCodecRoundTrips(f64, .standard(.float), {}, {}, &floatTestEdgeCases(f64));
}

test "standard utf8_codepoint" {
    try std.testing.expectEqual(1, Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{7F}', {}));
    try std.testing.expectEqual(2, Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{ff}', {}));
    try std.testing.expectEqual(3, Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{fff}', {}));
    try std.testing.expectEqual(4, Codec(u32).standard(.utf8_codepoint).encodedSize(.default, &'\u{fffff}', {}));
    try testCodecRoundTrips(u8, .standard(.utf8_codepoint), {}, {}, &@as([128]u8, std.simd.iota(u8, 128))); // ascii
    inline for (.{ u1, u2, u3, u4, u5, u6, u7, u8, u16, u21, u32 }) |AsciiInt| {
        const max_val = @min(127, std.math.maxInt(AsciiInt));
        const ascii_vals: [max_val + 1]AsciiInt = std.simd.iota(AsciiInt, max_val + 1);
        try testCodecRoundTrips(
            AsciiInt,
            .standard(.utf8_codepoint),
            {},
            {},
            &ascii_vals,
        );
    }
    try testCodecRoundTrips(u21, .standard(.utf8_codepoint), {}, {}, &.{ 'à', 'á', 'é', 'è', 'ì', 'í', 'ò', 'ó', 'ù', 'ú' });
    try testCodecRoundTrips(u21, .standard(.utf8_codepoint), {}, {}, &.{ '\u{2100}', '\u{3100}', '\u{FFAAA}', '\u{FFFFF}', '\u{FFFFF}' });
}

test "standard optional" {
    try testCodecRoundTrips(?void, .standard(.optional(.empty)), {}, null, &.{ null, {}, null, {}, null, {} });
    try testCodecRoundTrips(?bool, .standard(.optional(.boolean)), {}, null, &.{
        null, false, null, true, null, true,
        null, false, true, true, null, false,
    });
    try testCodecRoundTrips(?u32, .standard(.optional(.int)), {}, null, &.{ null, 4, null, 10000, null, 100000000 });
    try testCodecRoundTrips(?i64, .standard(.optional(.int)), {}, null, &.{ null, -7, null, 20000, null, -100000000 });

    const config: Config = .cfg(.little, .varint);
    try testEncodedBytesAndRoundTrip(?u32, .standard(.optional(.int)), .{
        .config = config,
        .enc_ctx = {},
        .dec_ctx = null,
        .original = 3,
        .expected_bytes = "\x01" ++ "\x03",
    });
    try testEncodedBytesAndRoundTrip(?u32, .standard(.optional(.int)), .{
        .config = config,
        .enc_ctx = {},
        .dec_ctx = null,
        .original = null,
        .expected_bytes = "\x00",
    });
    try testEncodedBytesAndRoundTrip(?u32, .standard(.optional(.int)), .{
        .config = config,
        .enc_ctx = {},
        .dec_ctx = null,
        .original = 251,
        .expected_bytes = "\x01" ++ "\xFB\xFB\x00",
    });
}

test "standard tuple" {
    const S = struct {
        a: u32,
        b: f64,

        const bk_codec: Codec(@This()) = .standard(.tuple(.{
            .a = .int,
            .b = .float,
        }));
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
    try testCodecRoundTrips(S, S.bk_codec, {}, null, &struct_test_edge_cases);

    try testEncodedBytesAndRoundTrip(
        S,
        S.bk_codec,
        .{
            .config = .cfg(.little, .varint),
            .enc_ctx = {},
            .dec_ctx = null,
            .original = .{ .a = 1, .b = 0 },
            .expected_bytes = "\x01" ++ std.mem.toBytes(@as(f64, 0)),
        },
    );
}

test "standard taggedUnion" {
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

        const bk_codec: Codec(@This()) = .standard(.taggedUnion(null, .{
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

    try testCodecRoundTrips(U, U.bk_codec, {}, null, &.{
        .void,
        .{ .char = 42 },
        .{ .int = 1111111111 },
        .{ .float = -7 },
        .{ .record = .{ .a = 1, .b = 2, .c = .foo } },
    });
}

test "standard byte_array" {
    try testCodecRoundTrips([3]u8, .standard(.byte_array), {}, {}, &.{ "foo".*, "bar".*, "baz".* });
}

test "standard array" {
    try testCodecRoundTrips([2]u64, .standard(.array(.int)), {}, null, @ptrCast(&intTestEdgeCases(u64) ++ intTestEdgeCases(u64)));
    try testCodecRoundTrips([2]u64, .standard(.array(.int)), {}, null, &.{
        .{ 1, 2 },
        .{ 61, 313131 },
        @splat(111111111),
    });

    try testCodecRoundTrips([2]f32, .standard(.array(.float)), {}, {}, @ptrCast(&floatTestEdgeCases(f32) ++ floatTestEdgeCases(f32)));
    try testCodecRoundTrips([2]f64, .standard(.array(.float)), {}, {}, @ptrCast(&floatTestEdgeCases(f64) ++ floatTestEdgeCases(f64)));
    try testCodecRoundTrips(@Vector(2, f32), .standard(.array(.float)), {}, {}, &.{
        .{ -1.0, 2 },
        .{ 61, -313131 },
        @splat(111111111.0),
    });
}

test "standard singleItemPtr" {
    try testCodecRoundTrips(*const u32, .standard(.singleItemPtr(.int)), {}, null, &.{
        &0, &1, &2, &10000, &std.math.maxInt(u32),
    });
}

test "standard byte_slice" {
    try testCodecRoundTrips([]const u8, .standard(.byte_slice), {}, {}, &.{
        &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 }, "foo",  "bar",  "baz",
        &.{ 127, std.math.maxInt(u8) },  "fizz", "buzz", "fizzbuzz",
    });
}

test "standard slice" {
    try testCodecRoundTrips([]const u32, .standard(.slice(.int)), {}, null, &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5, 6 },
        &.{ 7, 8, 9, 10, 11 },
        &.{ 12, 13, 14, 15, 16, 17 },
        &.{ 18, 19, 20, 21, 22, 23, 24 },
        &.{ 25, 26, 27, 28, 29, 30, 31, 32 },
    });
}

test "standard byte_array_ptr" {
    try testCodecRoundTrips(*const [3]u8, .standard(.byte_array_ptr), {}, {}, &.{
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

test "standard arrayPtr" {
    try testCodecRoundTrips(*const [3]u32, .standard(.arrayPtr(.int)), {}, null, &.{
        &.{ 0, 1, 2 },
        &.{ 3, 4, 5 },
        &.{ 7, 8, 9 },
        &.{ 12, 13, 14 },
        &.{ 18, 19, 20 },
        &.{ 25, 26, 27 },
    });
}

test "standard arrayList" {
    const gpa = std.testing.allocator;

    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try testCodecRoundTrips(std.ArrayList(u32), .standard(.arrayList(.int)), {}, null, &.{
        .empty,
        .fromOwnedSlice(try arena.dupe(u32, &.{ 1, 2, 3 })),
        .fromOwnedSlice(try arena.dupe(u32, &intTestEdgeCases(u32))),
    });
    try testEncodedBytesAndRoundTrip(
        std.ArrayList(u16),
        .standard(.arrayList(.int)),
        .{
            .config = .cfg(.little, .varint),
            .enc_ctx = {},
            .dec_ctx = null,
            .original = .fromOwnedSlice(try arena.dupe(u16, &.{ 0, 1, 250, 251 })),
            .expected_bytes = &[_]u8{4} ++ .{0} ++ .{1} ++ .{250} ++ .{ 251, 251, 0 },
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

    const str_array_list_codec: Codec(std.ArrayList([]const u8)) = .standard(.arrayList(.byte_slice));
    _ = try str_array_list_codec.decodeSliceInto(
        .{2} ++ .{4} ++ "fizz" ++ .{4} ++ "buzz",
        gpa,
        .{ .endian = .little, .int = .varint },
        &list,
        {},
    );
    try std.testing.expectEqualDeep(&[_][]const u8{ "fizz", "buzz" }, list.items);
}

test "standard arrayHashMap" {
    const gpa = std.testing.allocator;

    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const compare_ctx = struct {
        pub fn compare(expected: anytype, actual: anytype) !bool {
            const T = @TypeOf(expected, actual);
            if (ArrayHashMapInfo.from(T) != null) {
                try utils.testing.expectEqualDeepWithOverrides(expected.keys(), actual.keys(), @This());
                try utils.testing.expectEqualDeepWithOverrides(expected.values(), actual.values(), @This());
                return true;
            }
            return false;
        }
    };

    const MapU32U32 = std.AutoArrayHashMapUnmanaged(u32, u32);
    try testCodecRoundTripsInner(
        MapU32U32,
        .standard(.arrayHashMap(.int, .int)),
        {},
        null,
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
        .standard(.arrayHashMap(.byte_slice, .int)),
        .{
            .config = lev,
            .enc_ctx = {},
            .dec_ctx = null,
            .original = try initArrayHashMap(arena, MapStrU16, &.{ .{ "foo", 2 }, .{ "bar", 4 } }),
            .expected_bytes = encIntLit(lev, 2) ++
                (encStrLit(lev, "foo") ++ encIntLit(lev, 2)) ++
                (encStrLit(lev, "bar") ++ encIntLit(lev, 4)),
        },
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
        .standard(.arrayHashMap(.byte_slice, .int));
    _ = try map_str_u16_codec.decodeSliceInto(
        encIntLit(lev, 2) ++
            (encStrLit(lev, "big") ++ encIntLit(lev, 350)) ++
            (encStrLit(lev, "small") ++ encIntLit(lev, 400)),
        gpa,
        lev,
        &list,
        null,
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
        null,
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
        Codec(u32).standard(.int).decodeSliceExact((&overlong_varint_src)[0..1], null, config, null),
    );
    try std.testing.expectError(
        error.Overlong,
        Codec(u32).standard(.int).decodeSliceExact(&overlong_varint_src, null, config, null),
    );
    try std.testing.expectEqual(
        250,
        Codec(u32).standard(.int).decodeSliceIgnoreLength(&overlong_varint_src, null, config, null),
    );
}

test "optional slice memory re-use" {
    const gpa = std.testing.allocator;

    const codec: Codec(?[]const u8) = .standard(.optional(.byte_slice));

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

        const bk_codec: Codec(@This()) = .standard(.taggedUnion(.a, .{
            .a = .arrayList(.byte),
            .b = .byte_slice,
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

fn TestEncodedBytesAndRoundTripParams(comptime T: type, codec: Codec(T)) type {
    return struct {
        config: Config,
        enc_ctx: codec.EncodeCtx,
        dec_ctx: codec.DecodeCtx,
        original: T,
        expected_bytes: []const u8,
    };
}

/// Test that `value` encodes into the same bytes as `expected`, and then
/// also test whether `expected` decodes back into the same as `value`.
fn testEncodedBytesAndRoundTrip(
    comptime T: type,
    codec: Codec(T),
    params: TestEncodedBytesAndRoundTripParams(T, codec),
) !void {
    try testEncodedBytesAndRoundTripInner(T, codec, params, struct {
        pub fn compare(_: anytype, _: anytype) !bool {
            return false;
        }
    });
}

fn testEncodedBytesAndRoundTripInner(
    comptime T: type,
    codec: Codec(T),
    params: TestEncodedBytesAndRoundTripParams(T, codec),
    /// Expects methods:
    /// * `fn compare(expected: anytype, actual: @TypeOf(expected)) !bool`:
    ///   Should return true if the values were compared, and otherwise false
    ///   to fall back to default handling of comparison.
    compare_ctx: anytype,
) !void {
    const actual_bytes = try codec.encodeAlloc(
        std.testing.allocator,
        params.config,
        &params.original,
        params.enc_ctx,
    );
    defer std.testing.allocator.free(actual_bytes);
    try std.testing.expectEqualSlices(u8, params.expected_bytes, actual_bytes);

    const actual_value = codec.decodeSliceExact(actual_bytes, std.testing.allocator, params.config, params.dec_ctx);
    defer if (actual_value) |*unwrapped| codec.free(std.testing.allocator, unwrapped, params.dec_ctx) else |_| {};
    try utils.testing.expectEqualDeepWithOverrides(params.original, actual_value, compare_ctx);
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
    var buffer: std.ArrayList(u8) = .empty;
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
            try utils.testing.expectEqualDeepWithOverrides(expected, actual, compare_ctx);
        }
        try std.testing.expectEqual(0, encoded_reader.bufferedLen());
    }
}

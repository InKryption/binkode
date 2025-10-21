const std = @import("std");

pub fn encode(
    value: u256,
    buffer: *[IntKind.fullEncodedLen(.maximum)]u8,
    endian: std.builtin.Endian,
) IntKind {
    const kind: IntKind = .fromValue(value);
    switch (kind) {
        inline .u8, .u16, .u32, .u64, .u128, .u256 => |ikind| {
            const int: ikind.Type() = @intCast(value);
            buffer[0] = if (comptime ikind.firstByte()) |first_byte| first_byte else int;
            if (comptime ikind.remainingLen()) |rem_len| {
                buffer[1..][0..rem_len].* = @bitCast(std.mem.nativeTo(ikind.Type(), int, endian));
            }
        },
    }
    return kind;
}

pub fn decodeReader(
    reader: *std.Io.Reader,
    endian: std.builtin.Endian,
) std.Io.Reader.Error!u256 {
    const first_byte = first_byte: {
        var first_byte: u8 = undefined;
        try reader.readSliceAll((&first_byte)[0..1]);
        break :first_byte first_byte;
    };
    const kind: IntKind = .fromFirstByte(first_byte);
    const rem_len = kind.remainingLen() orelse return first_byte;

    var int_bytes_buffer: [IntKind.fullEncodedLen(.maximum)]u8 = undefined;
    const int_bytes = int_bytes_buffer[0..rem_len];
    try reader.readSliceAll(int_bytes);

    return kind.decode(int_bytes, endian);
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

    /// The maximum possible encoded representation.
    pub const maximum: IntKind = .u256;

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

    pub const FullEncodedLen = std.math.IntFittingRange(1, 1 + remainingLen(.maximum) orelse 0);

    pub fn fullEncodedLen(kind: IntKind) std.math.IntFittingRange(1, 1 + (remainingLen(.maximum) orelse 0)) {
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

    pub const RemainingLen = std.math.IntFittingRange(0, 32);

    /// Returns the number of bytes following the first byte which represent the encoded integer,
    /// or null if `kind == .u8`, meaning the first byte is the integer value.
    pub fn remainingLen(kind: IntKind) ?RemainingLen {
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
    pub fn decode(kind: IntKind, int_bytes: []const u8, endian: std.builtin.Endian) u256 {
        std.debug.assert(kind.remainingLen().? == int_bytes.len);
        return switch (kind) {
            .u8 => unreachable,
            inline .u16, .u32, .u64, .u128, .u256 => |ikind| {
                const T = ikind.Type();
                const len = comptime ikind.remainingLen().?;
                const int: T = @bitCast(int_bytes[0..len].*);
                return std.mem.nativeTo(T, int, endian);
            },
        };
    }
};

pub inline fn encodedLiteral(
    comptime endian: std.builtin.Endian,
    comptime value: u256,
) *const [IntKind.fullEncodedLen(.fromValue(value))]u8 {
    comptime {
        var buffer: [IntKind.fullEncodedLen(.maximum)]u8 = undefined;
        const kind = encode(value, &buffer, endian);
        const encoded_bytes = buffer[0..kind.fullEncodedLen()].*;
        return &encoded_bytes;
    }
}

pub const zigzag = struct {
    pub fn SignedAsUnsigned(comptime Signed: type) type {
        const signed_info = @typeInfo(Signed).int;
        switch (signed_info.signedness) {
            .signed => {},
            .unsigned => @compileError("Expected signed integer, got " ++ @typeName(Signed)),
        }
        return @Type(.{ .int = .{
            .bits = signed_info.bits,
            .signedness = .unsigned,
        } });
    }

    /// If `Int` is signed, returns `signedToUnsigned(Int, int)`.
    /// If `Int` is unsigned, returns `int`.
    pub fn anyToUnsigned(comptime Int: type, int: Int) switch (@typeInfo(Int).int.signedness) {
        .signed => SignedAsUnsigned(Int),
        .unsigned => Int,
    } {
        return switch (@typeInfo(Int).int.signedness) {
            .signed => signedToUnsigned(Int, int),
            .unsigned => int,
        };
    }

    /// Encodes a signed integer as an unsigned integer, such that values
    /// which are closer to zero are mapped to a smaller unsigned integer.
    /// This is used in the varint encoding scheme, where otherwise all
    /// negative values would have a very large encoded representation.
    /// NOTE: for unsigned integers, simply returns `signed`, which is
    /// actually unsigned despite its namesake in that circumstance.
    pub fn signedToUnsigned(comptime Signed: type, signed: Signed) SignedAsUnsigned(Signed) {
        const Unsigned = SignedAsUnsigned(Signed);
        const unsigned: Unsigned = @bitCast(signed);
        if (signed == 0) return unsigned;
        if (signed > 0) return unsigned * 2;
        if (signed < 0) return ~unsigned * 2 + 1;
        unreachable;
    }

    /// Inverse of `signedToUnsigned`.
    pub fn signedFromUnsigned(comptime Signed: type, unsigned: SignedAsUnsigned(Signed)) Signed {
        if (unsigned == 0) return 0;
        const plus_one_bit: u1 = @intCast(unsigned & 1);
        return switch (plus_one_bit) {
            0 => @bitCast(@divExact(unsigned, 2)),
            1 => @bitCast(~@divExact(unsigned - 1, 2)),
        };
    }
};

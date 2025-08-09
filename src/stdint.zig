const std = @import("std");
const bk = @import("binkode.zig");
const zigzag = bk.varint.zigzag;

/// Returns a namespace providing methods that encode/decode an integer in canonical bincode format.
/// These methods presume
pub fn StdInt(comptime V: type) type {
    const Int, const signedness = blk: {
        const int_info = @typeInfo(V).int;
        const encoded_bits = switch (int_info.bits) {
            0 => @compileError("This codec does not support zero-sized types."),
            (0 + 1)...8 => @compileError("This codec does not support byte-sized types."),
            (8 + 1)...16 => 16,
            (16 + 1)...32 => 32,
            (32 + 1)...64 => 64,
            (64 + 1)...128 => 128,
            (128 + 1)...256 => 256,
            else => @compileError("This codec does not support integers of type " ++ @typeName(V)),
        };

        const Int = switch (V) {
            usize => u64,
            isize => i64,
            else => std.meta.Int(int_info.signedness, encoded_bits),
        };
        break :blk .{ Int, int_info.signedness };
    };
    return struct {
        pub fn encode(writer: *std.Io.Writer, options: bk.Options, value: Int) bk.EncodeError!void {
            const int_encoding: bk.IntEncoding = options.int;
            switch (int_encoding) {
                .fixint => {
                    try writer.writeInt(Int, value, options.endian);
                },
                .varint => {
                    var buffer: [bk.varint.IntKind.fullEncodedLen(.maximum)]u8 = undefined;
                    const int_kind = bk.varint.encode(switch (signedness) {
                        .signed => zigzag.signedToUnsigned(Int, value),
                        .unsigned => value,
                    }, &buffer, options.endian);
                    try writer.writeAll(buffer[0..int_kind.fullEncodedLen()]);
                },
            }
        }

        pub fn decode(reader: *std.Io.Reader, options: bk.Options) bk.DecodeError!V {
            const int_encoding: bk.IntEncoding = options.int;
            switch (int_encoding) {
                .fixint => {
                    var int_bytes: [@sizeOf(Int)]u8 = undefined;
                    try reader.readSliceAll(&int_bytes);
                    const int = std.mem.readInt(Int, &int_bytes, options.endian);
                    if (int > std.math.maxInt(V)) return error.DecodeFailed;
                    return @intCast(int);
                },
                .varint => {
                    const raw_int = try bk.varint.decodeReader(reader, options.endian);
                    switch (signedness) {
                        .signed => {
                            const EncodedInt = zigzag.SignedAsUnsigned(Int);
                            if (raw_int > std.math.maxInt(EncodedInt)) return error.DecodeFailed;
                            const encoded_int: EncodedInt = @intCast(raw_int);
                            const int: Int = zigzag.signedFromUnsigned(Int, encoded_int);
                            if (int > std.math.maxInt(V)) return error.DecodeFailed;
                            return @intCast(int);
                        },
                        .unsigned => {
                            if (raw_int > std.math.maxInt(V)) return error.DecodeFailed;
                            return @intCast(raw_int);
                        },
                    }
                },
            }
        }
    };
}

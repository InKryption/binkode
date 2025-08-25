const std = @import("std");

const ArrayHashMapInfo = @This();
Element: type,
alignment: std.mem.Alignment,

pub fn from(comptime T: type) ?ArrayHashMapInfo {
    if (@typeInfo(T) != .@"struct") return null;

    if (!@hasDecl(T, "Slice")) return null;
    if (@TypeOf(&T.Slice) != *const type) return null;
    const Slice = T.Slice;
    const ptr_info = switch (@typeInfo(Slice)) {
        .pointer => |ptr_info| ptr_info,
        else => return null,
    };
    if (ptr_info.size != .slice) return null;
    const alignment: std.mem.Alignment = .fromByteUnits(ptr_info.alignment);
    const Expected = std.array_list.Aligned(ptr_info.child, alignment);
    if (T != Expected) return null;
    return .{
        .Element = ptr_info.child,
        .alignment = alignment,
    };
}

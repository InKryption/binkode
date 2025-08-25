//! Small utility for reflecting some standard library types.

pub const ArrayListInfo = @import("std_reflect/ArrayListInfo.zig");
pub const ArrayHashMapInfo = @import("std_reflect/ArrayHashMapInfo.zig");

comptime {
    _ = ArrayListInfo;
    _ = ArrayHashMapInfo;
}

//! Small utility for reflecting some standard library types.

pub const ArrayListInfo = @import("std_reflect/ArrayListInfo.zig");
pub const ArrayHashMapInfo = @import("std_reflect/ArrayHashMapInfo.zig");

comptime {
    _ = ArrayListInfo;
    _ = ArrayHashMapInfo;
}

/// Small utility for tracking how many types in a set of types are void or optional.
pub const FieldGroupKind = enum(u2) {
    /// All fields are void.
    all_void = 0,
    /// Some fields are not void, but are optional.
    all_opt_or_void = 1,
    /// Some fields are not void, and are also not optional.
    some_required = 2,

    pub fn fromType(comptime T: type) FieldGroupKind {
        return switch (@typeInfo(T)) {
            .void => .all_void,
            .optional => .all_opt_or_void,
            else => .some_required,
        };
    }

    pub fn max(a: FieldGroupKind, b: FieldGroupKind) FieldGroupKind {
        return @enumFromInt(@max(@intFromEnum(a), @intFromEnum(b)));
    }
};

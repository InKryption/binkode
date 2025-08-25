const std = @import("std");

const ArrayHashMapInfo = @This();
K: type,
V: type,
Context: type,
store_hash: bool,

pub fn from(comptime T: type) ?ArrayHashMapInfo {
    if (@typeInfo(T) != .@"struct") return null;

    if (!@hasDecl(T, "KV")) return null;
    if (@TypeOf(&T.KV) != *const type) return null;
    const KV = T.KV;

    if (@typeInfo(KV) != .@"struct") return null;
    if (!@hasField(KV, "key")) return null;
    if (!@hasField(KV, "value")) return null;
    const K = @FieldType(KV, "key");
    const V = @FieldType(KV, "value");

    if (!@hasDecl(T, "Hash")) return null;
    if (@TypeOf(&T.Hash) != *const type) return null;
    const store_hash = switch (T.Hash) {
        u32 => true,
        void => false,
        else => return null,
    };

    if (!@hasDecl(T, "popContext")) return null;
    const pop_ctx_fn_info = switch (@typeInfo(@TypeOf(T.popContext))) {
        .@"fn" => |fn_info| fn_info,
        else => return null,
    };
    if (pop_ctx_fn_info.params.len != 2) return null;
    const Context = pop_ctx_fn_info.params[1].type orelse return null;

    if (T != std.ArrayHashMapUnmanaged(K, V, Context, store_hash)) return null;

    return .{
        .K = K,
        .V = V,
        .Context = Context,
        .store_hash = store_hash,
    };
}

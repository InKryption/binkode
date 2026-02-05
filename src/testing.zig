const std = @import("std");
const bk = @import("binkode.zig");

pub const TestExpectedEqualError = error{TestExpectedEqual};

pub fn Comparator(comptime V: type) type {
    return struct {
        Ctx: type,
        expectEqualFn: fn (
            /// Must be a value of type `Ctx`.
            ctx: anytype,
            expected: *const V,
            actual: *const V,
        ) TestExpectedEqualError!void,
        const ComparatorSelf = @This();

        pub fn withCtx(self: ComparatorSelf, ctx: self.Ctx) WithCtx(self) {
            return .{ .ctx = ctx };
        }

        pub fn WithCtx(comparator: ComparatorSelf) type {
            return struct {
                ctx: comparator.Ctx,
                const WithCtxSelf = @This();

                pub fn expectEqual(
                    self: *const WithCtxSelf,
                    expected: V,
                    actual: V,
                ) TestExpectedEqualError!void {
                    try self.expectEqualNoCopy(&expected, &actual);
                }

                pub fn expectEqualNoCopy(
                    self: *const WithCtxSelf,
                    expected: *const V,
                    actual: *const V,
                ) TestExpectedEqualError!void {
                    return comparator.expectEqualFn(self.ctx, expected, actual);
                }
            };
        }

        pub fn expectEqual(
            self: ComparatorSelf,
            expected: V,
            actual: V,
        ) TestExpectedEqualError!void {
            try self.expectEqualNoCopy(&expected, &actual);
        }

        pub fn expectEqualNoCopy(
            self: ComparatorSelf,
            expected: *const V,
            actual: *const V,
        ) TestExpectedEqualError!void {
            if (self.Ctx != void) @compileError("Use .withCtx(ctx) instead");
            return self.expectEqualFn({}, expected, actual);
        }

        /// Shallow comparison context.
        pub const shallow: ComparatorSelf = .implement(void, struct {
            pub fn expectEqual(
                _: void,
                expected: *const V,
                actual: *const V,
            ) TestExpectedEqualError!void {
                try std.testing.expectEqual(expected.*, actual.*);
            }
        });

        /// Shallow comparison context.
        pub const deep: ComparatorSelf = .implement(void, struct {
            pub fn expectEqual(
                _: void,
                expected: *const V,
                actual: *const V,
            ) TestExpectedEqualError!void {
                try std.testing.expectEqualDeep(expected.*, actual.*);
            }
        });

        const ptr_info = switch (@typeInfo(V)) {
            .pointer => |info| info,
            else => @compileError(@typeName(V) ++ " is not a pointer."),
        };
        const SliceElem = switch (ptr_info.size) {
            .slice => ptr_info.child,
            .many => if (ptr_info.sentinel_ptr != null)
                ptr_info.child
            else
                @compileError(@typeName(V) ++ " cannot be sliced (no sentinel)."),
            .one => switch (@typeInfo(ptr_info.child)) {
                .array => |array_info| array_info.child,
                else => @compileError(@typeName(V) ++ " is not a slice."),
            },
            else => @compileError(@typeName(V) ++ " is not a slice."),
        };

        pub fn forSlice(elem: Comparator(SliceElem)) ComparatorSelf {
            return .implement(void, struct {
                pub fn expectEqual(
                    elem_ctx: elem.Ctx,
                    expected: *const V,
                    actual: *const V,
                ) TestExpectedEqualError!void {
                    try std.testing.expectEqual(expected.*.len, actual.*.len);
                    for (expected.*, actual.*, 0..) |*expected_item, *actual_item, index| {
                        errdefer testPrint(
                            "Difference occurred at entry {d}: {any} != {any}",
                            .{ index, actual_item.*, expected_item.* },
                        );
                        try elem.withCtx(elem_ctx).expectEqualNoCopy(expected_item, actual_item);
                    }
                }
            });
        }

        const al_info = bk.std_reflect.ArrayListInfo.from(V) orelse @compileError(
            @typeName(V) ++ " is not an `ArrayList`.",
        );
        pub fn forArrayList(elem: Comparator(al_info.Element)) ComparatorSelf {
            return .implement(elem.Ctx, struct {
                pub fn expectEqual(
                    elem_ctx: elem.Ctx,
                    expected: *const V,
                    actual: *const V,
                ) TestExpectedEqualError!void {
                    try std.testing.expectEqual(expected.items.len, actual.items.len);
                    for (expected.items, actual.items, 0..) |*expected_item, *actual_item, index| {
                        errdefer testPrint(
                            "Difference occurred at entry {d}: {any} != {any}",
                            .{ index, actual_item.*, expected_item.* },
                        );
                        try elem.withCtx(elem_ctx).expectEqualNoCopy(expected_item, actual_item);
                    }
                }
            });
        }

        const hm_info = bk.std_reflect.ArrayHashMapInfo.from(V) orelse @compileError(
            @typeName(V) ++ " is not an `ArrayHashMap`.",
        );

        pub fn ArrayHashMapCtxs(
            comptime KeyCtx: type,
            comptime ValCtx: type,
        ) type {
            return struct {
                key: KeyCtx,
                val: ValCtx,
            };
        }

        pub fn forArrayHashMap(
            key_cmp: Comparator(hm_info.K),
            val_cmp: Comparator(hm_info.V),
        ) ComparatorSelf {
            const KeyValCtxs = ArrayHashMapCtxs(key_cmp.Ctx, val_cmp.Ctx);
            const kv_fgk: bk.std_reflect.FieldGroupKind = .max(
                .fromType(key_cmp.Ctx),
                .fromType(val_cmp.Ctx),
            );
            const CtxParam = switch (kv_fgk) {
                .all_void => void,
                .all_opt_or_void => ?KeyValCtxs,
                .some_required => KeyValCtxs,
            };
            return .implement(CtxParam, struct {
                pub fn expectEqual(
                    maybe_kv_ctx: CtxParam,
                    expected: *const V,
                    actual: *const V,
                ) TestExpectedEqualError!void {
                    const key_ctx, const val_ctx = switch (kv_fgk) {
                        .all_void => .{ {}, {} },
                        .all_opt_or_void => if (maybe_kv_ctx) |kv_ctx| .{ kv_ctx.key, kv_ctx.val },
                        .some_required => .{ maybe_kv_ctx.key, maybe_kv_ctx.val },
                    };

                    try std.testing.expectEqual(expected.count(), actual.count());
                    for (
                        expected.keys(),
                        actual.keys(),
                        expected.values(),
                        actual.values(),
                        0..,
                    ) |*expected_key, *actual_key, *expected_val, *actual_val, index| {
                        errdefer testPrint(
                            "Difference occurred at entry {d}: .{{ {any}, {any} }} != .{{ {any}, {any} }}",
                            .{
                                index,
                                expected_key.*,
                                expected_val.*,
                                actual_key.*,
                                actual_val.*,
                            },
                        );
                        try key_cmp.withCtx(key_ctx).expectEqualNoCopy(expected_key, actual_key);
                        try val_cmp.withCtx(val_ctx).expectEqualNoCopy(expected_val, actual_val);
                    }
                }
            });
        }

        const optional_info = switch (@typeInfo(V)) {
            .optional => |info| info,
            else => @compileError(@typeName(V) ++ " is not an error union."),
        };

        pub fn forOptional(
            payload: Comparator(optional_info.payload),
        ) ComparatorSelf {
            return .implement(payload.Ctx, struct {
                pub fn expectEqual(
                    pl_ctx: payload.Ctx,
                    expected: *const V,
                    actual: *const V,
                ) TestExpectedEqualError!void {
                    if (expected.*) |*expected_pl| {
                        if (actual.*) |*actual_pl| {
                            try payload.withCtx(pl_ctx).expectEqualNoCopy(expected_pl, actual_pl);
                        } else |actual_err| {
                            testPrint(
                                "Expected {any}, got {s}.",
                                .{ expected_pl.*, @errorName(actual_err) },
                            );
                            return error.TestExpectedEqual;
                        }
                    } else {
                        if (actual.*) |*actual_pl| {
                            testPrint(
                                "Expected null, got {any}.",
                                .{actual_pl.*},
                            );
                            return error.TestExpectedEqual;
                        }
                    }
                }
            });
        }

        const error_union_info = switch (@typeInfo(V)) {
            .error_union => |info| info,
            else => @compileError(@typeName(V) ++ " is not an error union."),
        };

        pub fn forErrorUnion(
            payload: Comparator(error_union_info.payload),
        ) ComparatorSelf {
            return .implement(payload.Ctx, struct {
                pub fn expectEqual(
                    pl_ctx: payload.Ctx,
                    expected: *const V,
                    actual: *const V,
                ) TestExpectedEqualError!void {
                    if (expected.*) |*expected_pl| {
                        if (actual.*) |*actual_pl| {
                            try payload.withCtx(pl_ctx).expectEqualNoCopy(expected_pl, actual_pl);
                        } else |actual_err| {
                            testPrint(
                                "Expected {any}, got {s}.",
                                .{ expected_pl.*, @errorName(actual_err) },
                            );
                            return error.TestExpectedEqual;
                        }
                    } else |expected_err| {
                        if (actual.*) |*actual_pl| {
                            testPrint(
                                "Expected {any}, got {any}.",
                                .{ expected_err, actual_pl.* },
                            );
                            return error.TestExpectedEqual;
                        } else |actual_err| {
                            try std.testing.expectEqual(expected_err, actual_err);
                        }
                    }
                }
            });
        }

        // --- helpers for implementation --- //

        pub fn implement(
            comptime Ctx: type,
            comptime methods: type,
        ) ComparatorSelf {
            const erased = struct {
                fn expectEqualFn(
                    ctx: anytype,
                    expected: *const V,
                    actual: *const V,
                ) TestExpectedEqualError!void {
                    if (@TypeOf(ctx) != Ctx) @compileError(
                        "Expected type " ++ @typeName(Ctx) ++ ", got " ++ @typeName(@TypeOf(ctx)),
                    );
                    try methods.expectEqual(ctx, expected, actual);
                }
            };
            return .{
                .Ctx = Ctx,
                .expectEqualFn = erased.expectEqualFn,
            };
        }
    };
}

pub fn testPrint(comptime fmt: []const u8, args: anytype) void {
    if (@inComptime()) {
        @compileError(std.fmt.comptimePrint(fmt, args));
    } else if (std.testing.backend_can_print) {
        std.debug.print(fmt ++ "\n", args);
    }
}

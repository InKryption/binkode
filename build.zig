const std = @import("std");
const Build = std.Build;

pub fn build(b: *Build) void {
    const is_root = b.pkg_hash.len == 0;

    const install_step = b.getInstallStep();
    const test_step = b.step("test", "All tests.");
    const unit_test_step = b.step("unit-test", "Unit tests.");
    const check_step = b.step("check", "Check step.");

    test_step.dependOn(unit_test_step);
    check_step.dependOn(install_step);

    // local dev-only options.
    // exposed modules should simply inherit these options when imported.
    const maybe_optimize = if (is_root) b.standardOptimizeOption(.{}) else null;
    const maybe_target = if (is_root) b.standardTargetOptions(.{}) else null;

    const binkode_mod = b.addModule("binkode", .{
        .root_source_file = b.path("src/binkode.zig"),
        .optimize = maybe_optimize,
        .target = maybe_target,
    });

    // remainder of the build graph is for local development.
    if (!is_root) return;
    const bin_opts: BinOptions = .fromBuildOptions(b);
    const filters = b.option([]const []const u8, "filter", "Filter(s) for tests.") orelse &.{};
    const force_llvm = b.option(bool, "force-llvm", "Force usage of the llvm backend.") orelse false;

    const unit_test_exe = b.addTest(.{
        .name = "unit-test",
        .root_module = binkode_mod,
        .filters = filters,
        .use_llvm = if (force_llvm) true else null,
    });

    const unit_test_out = addExeOutputs(b, .{
        .exe = unit_test_exe,
        .step = unit_test_step,
        .bin = bin_opts,
        .install = .{},
    });
    _ = unit_test_out;
}

const BinOptions = packed struct {
    install: bool,
    run: bool,

    fn fromBuildOptions(b: *Build) BinOptions {
        const no_bin = b.option(
            bool,
            "no-bin",
            "Don't install any of the binaries implied by the specified steps.",
        ) orelse false;
        const no_run = b.option(
            bool,
            "no-run",
            "Don't run any of the executables implied by the specified steps.",
        ) orelse false;
        return .{
            .install = !no_bin,
            .run = !no_run,
        };
    }
};

const ExeOutputs = struct {
    install: ?*Build.Step.InstallArtifact,
    run: ?*Build.Step.Run,
};

fn addExeOutputs(
    b: *Build,
    params: struct {
        exe: *Build.Step.Compile,
        step: *Build.Step,
        bin: BinOptions,
        install: Build.Step.InstallArtifact.Options,
    },
) ExeOutputs {
    const exe = params.exe;
    const step = params.step;
    const artifact_opts = params.bin;
    const install_opts = params.install;

    const maybe_exe_install = if (artifact_opts.install) b.addInstallArtifact(exe, install_opts) else null;
    const maybe_exe_run = if (artifact_opts.run) b.addRunArtifact(exe) else null;

    step.dependOn(&exe.step);
    if (maybe_exe_install) |exe_install| step.dependOn(&exe_install.step);
    if (maybe_exe_run) |exe_run| step.dependOn(&exe_run.step);

    const install_step = b.getInstallStep();
    install_step.dependOn(&exe.step);
    if (maybe_exe_install) |exe_install| install_step.dependOn(&exe_install.step);

    return .{
        .install = maybe_exe_install,
        .run = maybe_exe_run,
    };
}

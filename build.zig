const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});

    const optimize = b.standardOptimizeOption(.{});

    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lib = b.addLibrary(.{
        .linkage = .static,
        .name = "zig_ajtai",
        .root_module = lib_mod,
    });

    b.installArtifact(lib);

    const filters = b.option([]const []const u8, "filter", "filter based on name");

    const lib_unit_tests = b.addTest(.{
        .root_module = lib_mod,
        .filters = filters orelse &.{},
    });

    const run_lib_unit_tests = b.addRunArtifact(lib_unit_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_lib_unit_tests.step);
}

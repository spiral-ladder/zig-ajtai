//! Contains tests for `CyclotomicRing` and other operations.

fn test_ring_addition(
    comptime F: PrimeField,
    R: type,
    ring_coefficients_a: []F.T,
    ring_coefficients_b: []F.T,
    ring_coefficients_expected: []F.T,
) !void {
    const r = R.init();
    const expected = try r.elementFromSlice(std.testing.allocator, ring_coefficients_expected);
    defer expected.deinit();
    var a = try r.elementFromSlice(std.testing.allocator, ring_coefficients_a);
    var b = try r.elementFromSlice(std.testing.allocator, ring_coefficients_b);

    const got = try r.add(&a, &b);
    defer got.deinit();
    try std.testing.expectEqualSlices(F.M.Fe, expected.coefficients.items, got.coefficients.items);
}

test "ring addition" {
    const M = ff.Modulus(8);
    const D = 8;
    const E = 8;
    const q = 17;
    const F = PrimeField{ .M = M, .T = u8, .q = q };
    const m = comptime blk: {
        @setEvalBranchQuota(10_000);
        break :blk M.fromPrimitive(u8, q) catch unreachable;
    };
    const P = comptime try M.Fe.fromPrimitive(u8, m, try F.find2NPrimitiveRoot(D));
    const R = CyclotomicRing(.Strict, D, E, F, P);

    {
        var coefficients_a: [8]u8 = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8 };
        var coefficients_b: [8]u8 = [_]u8{ 2, 3, 4, 5, 6, 7, 8, 9 };
        var coefficients_res: [8]u8 = [_]u8{ 3, 5, 7, 9, 11, 13, 15, 0 };
        try test_ring_addition(F, R, &coefficients_a, &coefficients_b, &coefficients_res);
    }
    {
        var coefficients_a: [8]u8 = [_]u8{ 0, 0, 0, 0, 0, 0, 0, 0 };
        var coefficients_b: [8]u8 = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8 };
        var coefficients_res: [8]u8 = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8 };
        try test_ring_addition(F, R, &coefficients_a, &coefficients_b, &coefficients_res);
    }
    {
        var coefficients_a: [8]u8 = [_]u8{10} ** 8;
        var coefficients_b: [8]u8 = [_]u8{15} ** 8;
        var coefficients_res: [8]u8 = [_]u8{8} ** 8;
        try test_ring_addition(F, R, &coefficients_a, &coefficients_b, &coefficients_res);
    }
    {
        var coefficients_a: [8]u8 = [_]u8{ 0, 16, 0, 16, 0, 16, 0, 16 };
        var coefficients_b: [8]u8 = [_]u8{ 16, 0, 16, 0, 16, 0, 16, 0 };
        var coefficients_res: [8]u8 = [_]u8{16} ** 8;
        try test_ring_addition(F, R, &coefficients_a, &coefficients_b, &coefficients_res);
    }
}

fn test_ring_multiplication(
    R: type,
    comptime F: PrimeField,
    ring_coefficients_a: []F.T,
    ring_coefficients_b: []F.T,
    ring_coefficients_expected: []F.T,
) !void {
    const r = R.init();
    const expected = try r.elementFromSlice(std.testing.allocator, ring_coefficients_expected);
    defer expected.deinit();

    var a = try r.elementFromSlice(std.testing.allocator, ring_coefficients_a);
    defer a.deinit();
    var b = try r.elementFromSlice(std.testing.allocator, ring_coefficients_b);
    defer b.deinit();

    // Use naiveMul operation on the ring with element parameters
    const got = try r.naiveMul(std.testing.allocator, a, b);
    defer got.deinit();
    try std.testing.expectEqualSlices(F.M.Fe, expected.coefficients.items, got.coefficients.items);

    // Make copies for the NTT-based mul which modifies inputs
    var a_copy = try r.elementFromSlice(std.testing.allocator, ring_coefficients_a);
    defer a_copy.deinit();
    var b_copy = try r.elementFromSlice(std.testing.allocator, ring_coefficients_b);
    defer b_copy.deinit();

    // Use mul operation on the ring with element parameters
    const got_2 = try r.mul(std.testing.allocator, &a_copy, &b_copy);
    defer got_2.deinit();
    try std.testing.expectEqualSlices(F.M.Fe, expected.coefficients.items, got_2.coefficients.items);
}

test "ring multiplication" {
    const M = ff.Modulus(8);
    const D = 8;
    const E = 8;
    const q = 17;
    const F = PrimeField{ .M = M, .T = u8, .q = q };
    const m = comptime blk: {
        @setEvalBranchQuota(10_000);
        break :blk M.fromPrimitive(u8, q) catch unreachable;
    };
    const P = comptime try M.Fe.fromPrimitive(u8, m, try F.find2NPrimitiveRoot(D));
    const R = CyclotomicRing(.Strict, D, E, F, P);

    {
        // Basic multiplication: (1 + x) * x^2 = x^2 + x^3
        var coefficients_a: [8]u8 = [_]u8{ 1, 1, 0, 0, 0, 0, 0, 0 };
        var coefficients_b: [8]u8 = [_]u8{ 0, 0, 1, 0, 0, 0, 0, 0 };
        var coefficients_res: [8]u8 = [_]u8{ 0, 0, 1, 1, 0, 0, 0, 0 };
        try test_ring_multiplication(R, F, &coefficients_a, &coefficients_b, &coefficients_res);
    }
    {
        // Multiplication with zero polynomial
        var coefficients_a: [8]u8 = [_]u8{ 0, 0, 0, 0, 0, 0, 0, 0 };
        var coefficients_b: [8]u8 = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8 };
        var coefficients_res: [8]u8 = [_]u8{ 0, 0, 0, 0, 0, 0, 0, 0 };
        try test_ring_multiplication(R, F, &coefficients_a, &coefficients_b, &coefficients_res);
    }
    {
        // Multiplication with constant polynomial
        // (2) * (1 + 2x + 3x² + 4x³ + 5x⁴ + 6x⁵ + 7x⁶ + 8x⁷) = 2 + 4x + 6x² + 8x³ + 10x⁴ + 12x⁵ + 14x⁶ + 16x⁷
        var coefficients_a: [8]u8 = [_]u8{ 2, 0, 0, 0, 0, 0, 0, 0 };
        var coefficients_b: [8]u8 = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8 };
        var coefficients_res: [8]u8 = [_]u8{ 2, 4, 6, 8, 10, 12, 14, 16 };
        try test_ring_multiplication(R, F, &coefficients_a, &coefficients_b, &coefficients_res);
    }
    {
        // Multiplication wrap around
        // (1 + x^2 + x^4 + x^6) * (1 + x^2 + x^4 + x^6) = -2 + 2x^4 + 4x^6 = 15 + 2x⁴ + 4x⁶
        var coefficients_a: [8]u8 = [_]u8{ 1, 0, 1, 0, 1, 0, 1, 0 };
        var coefficients_b: [8]u8 = [_]u8{ 1, 0, 1, 0, 1, 0, 1, 0 };
        var coefficients_res: [8]u8 = [_]u8{ 15, 0, 0, 0, 2, 0, 4, 0 };
        try test_ring_multiplication(R, F, &coefficients_a, &coefficients_b, &coefficients_res);
    }
}

test "ring multiplication - kyber round 1 params" {
    const q = 7681;
    const T = u32;
    const M = ff.Modulus(@bitSizeOf(T));
    const F = PrimeField{ .M = M, .T = T, .q = q };
    const D = 256;

    const m = comptime blk: {
        @setEvalBranchQuota(100_000);
        break :blk M.fromPrimitive(T, q) catch unreachable;
    };
    const P = comptime try M.Fe.fromPrimitive(T, m, try F.find2NPrimitiveRoot(D));
    const R = CyclotomicRing(.Standard, D, null, F, P);

    var a: [D]T = [_]T{0} ** D;
    var b: [D]T = [_]T{0} ** D;
    var prng = std.Random.DefaultPrng.init(blk: {
        var seed: u64 = undefined;
        try std.posix.getrandom(std.mem.asBytes(&seed));
        break :blk seed;
    });
    const random = prng.random();

    const max_fe = m.sub(m.zero, m.one());
    const max = try max_fe.toPrimitive(T);
    for (0..D) |i| {
        a[i] = random.intRangeAtMost(T, 0, max);
        b[i] = random.intRangeAtMost(T, 0, max);
    }

    const r = R.init();
    const allocator = std.testing.allocator;
    const a_poly = try r.elementFromSlice(allocator, &a);
    defer a_poly.deinit();
    const b_poly = try r.elementFromSlice(allocator, &b);
    defer b_poly.deinit();

    // i'm lazy so for now we pass the result of naive mul here, even though we already do it in
    // `test_ring_multiplication`.
    const expected = try r.naiveMul(allocator, a_poly, b_poly);
    defer expected.deinit();
    var expected_coeffs: [D]T = [_]T{0} ** D;

    for (0..D) |i| {
        expected_coeffs[i] = try expected.coefficients.items[i].toPrimitive(T);
    }

    try test_ring_multiplication(R, F, &a, &b, &expected_coeffs);
}

const CyclotomicRing = ring.CyclotomicRing;
const inv = PrimeField.inv;
const find2NPrimitiveRoot = PrimeField.find2NPrimitiveRoot;

const PrimeField = @import("PrimeField.zig");
const ring = @import("ring.zig");

const std = @import("std");

const ArrayList = std.ArrayList;
const Allocator = std.mem.Allocator;

const ff = std.crypto.ff;

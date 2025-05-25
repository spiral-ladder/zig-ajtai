pub const PrimeField = struct {
    /// The `std.crypto.ff.Modulus` type.
    M: type,
    /// The integer type used to represent the field.
    T: type,
    /// The actual modulus `q` used in the `CyclotomicRing`.
    q: comptime_int,
};

/// Computes the multiplicative inverse of a field element using Fermat's Little Theorem.
/// For a field element a, a^(-1) = a^(p-2) mod p where p is the field modulus.
pub fn inv(comptime F: PrimeField, a: F.M.Fe) F.M.Fe {
    const m = F.M.fromPrimitive(F.T, F.q) catch unreachable;
    const p_minus_2: usize = F.q - 2;

    // Use binary exponentiation to compute a^(p-2)
    var result = m.one();
    var base = a;
    var exp = p_minus_2;

    while (exp > 0) {
        if (exp & 1 == 1) {
            result = m.mul(result, base);
        }
        base = m.mul(base, base);
        exp >>= 1;
    }

    return result;
}

/// Finds a primitive 2n-th root of unity in the field.
///
/// A primitive 2n-th root of unity ψ satisfies:
/// - ψ^n ≡ -1 (mod q)
/// - ψ^(2n) ≡ 1 (mod q)
///
/// This guarantees the existence of a 2D-th primitive root of unity for efficient NTT/iNTT.
pub fn find2NPrimitiveRoot(comptime F: PrimeField, comptime D: u128) !F.T {
    @setEvalBranchQuota(20_000);
    const m = F.M.fromPrimitive(F.T, F.q) catch unreachable;
    const d_fe = try F.M.Fe.fromPrimitive(F.T, m, D); // The degree of the polynomial X^D + 1
    const candidates = [_]F.T{ 2, 3, 5, 7, 11, 13, 17, 19, 23 };

    const exponent = try F.M.Fe.fromPrimitive(F.T, m, (F.q - 1) / (2 * D));

    const neg_one = m.sub(m.zero, m.one());
    for (candidates) |candidate| {
        if (candidate >= F.q) continue;

        const element = F.M.Fe.fromPrimitive(F.T, m, candidate) catch unreachable;

        const possible_root = try m.pow(element, exponent);
        // Verify this is indeed a primitive 2n-th root by checking if its n-th power is -1
        const powered = try m.pow(possible_root, d_fe);
        if (powered.eql(neg_one)) return possible_root.toPrimitive(F.T) catch unreachable;
    }

    // If no small candidates work, do an exhaustive search
    var candidate: F.T = 25; // Start after our initial candidates
    while (candidate < F.q) : (candidate += 1) {
        const element = F.M.Fe.fromPrimitive(F.T, m, candidate) catch unreachable;

        const possible_root = try m.pow(element, exponent);
        // Verify this is indeed a primitive 2n-th root by checking if its n-th power is -1
        const powered = try m.pow(possible_root, d_fe);
        if (powered.eql(neg_one)) return possible_root.toPrimitive(F.T) catch unreachable;
    }

    return error.CannotFindPrimitiveRoot;
}

/// Configures the compile-time checks that `CyclotomicRing` should do.
const RingModuloCfg = enum {
    /// Ensures q ≡ 1 (mod 2D).
    Standard,
    /// Ensures q ≡ 1 + 2E (mod 4E) for some E | D.
    Strict,
};

/// A CyclotomicRing defining elements of the ring Z_q[X]/(X^D + 1).
///
/// All operations done within the ring are performed modulo a prime q and the cyclotomic polynomial X^D + 1.
///
/// `C` - The configuration that decides the relationship between `F.q` and `D` or `E` for efficient NTTs
/// `D` - The degree of the cyclotomic polynomial X^D + 1
/// `E` - `E` is the parameter that ensures correct parameters for faster NTTs in the stricter setting
/// `F` - The `PrimeField` used for coefficients
/// `P` - The primitive root of unity used for NTTs
///
/// At compile-time, we check that:
/// 1) D is a power of two
/// 2) If `C` == `.Standard`, that
///      a) F.q ≡ 1 (mod 2D), or
///    If `C` == `.Strict`, that
///      a) F.q ≡ 1 + 2E (mod 4E) for some E | D
///         If q ≡ 1 + 2E (mod 4E), Rq ∼= F_{q^D/E}^E via the Number Theoretic Transform (NTT).
///      b) E divides D
///
/// These conditions ensure the existence of appropriate roots of unity for the negatively wrapped convolution-based NTT.
pub fn CyclotomicRing(
    comptime C: RingModuloCfg,
    comptime D: u128,
    comptime E: ?u128,
    comptime F: PrimeField,
    comptime P: F.M.Fe,
) type {
    comptime std.debug.assert(std.math.isPowerOfTwo(D));
    switch (C) {
        .Standard => if ((F.q - 1) % (2 * D) != 0) {
            const str = std.fmt.comptimePrint("F.q is not congruent to 1 (mod 2D). F.q = {}, D = {}, remainder = {}\n", .{ F.q, D, (F.q - 1 % (2 * D)) });
            @compileError(str);
        },
        .Strict => {
            comptime std.debug.assert(E != null);
            const e = E.?;
            comptime std.debug.assert(D % e == 0);
            const lhs = F.q % (4 * e);
            const rhs = (1 + 2 * e) % (4 * e);
            if (lhs != rhs) {
                const str = std.fmt.comptimePrint("F.q is not congruent to 1 + 2E (mod 4E). F.q % (4 * E) = {}, (1 + 2 * E) % (4 * E) = {}\n", .{ lhs, rhs });
                @compileError(str);
            }
        },
    }

    return struct {
        pub const Element = RingElement;
        pub const T = F.T;

        const Self = @This();

        const RingElement = struct {
            coefficients: ArrayList(F.M.Fe),

            pub fn deinit(self: RingElement) void {
                self.coefficients.deinit();
            }
        };

        m: F.M,

        /// Initialises an instance of the `CyclotomicRing` with a `ff.Modulus`.
        pub fn init() Self {
            const m = F.M.fromPrimitive(F.T, F.q) catch unreachable;

            return .{
                .m = m,
            };
        }

        /// Creates a `RingElement` of the `CyclotomicRing`. Allocates a backing `ArrayList`.
        ///
        /// Deinitialize with `Element.deinit`.
        pub fn elementFromSlice(self: Self, allocator: Allocator, slice: []F.T) !Element {
            var coefficients = ArrayList(F.M.Fe).initCapacity(allocator, slice.len) catch unreachable;
            errdefer coefficients.deinit();
            for (slice) |c| {
                const fe = F.M.Fe.fromPrimitive(F.T, self.m, c) catch unreachable;
                coefficients.appendAssumeCapacity(fe);
            }
            return .{ .coefficients = coefficients };
        }

        /// Adds two `RingElement`s point-wise.
        ///
        /// Note: this function adds `b` to `a` in place and frees `b`'s backing memory.
        pub fn add(self: Self, a: *Element, b: *Element) !Element {
            var out = a;
            const b_slice = b.coefficients.items;
            defer b.deinit();
            for (0..a.coefficients.items.len) |i| {
                out.coefficients.items[i] = self.m.add(a.coefficients.items[i], b_slice[i]);
            }

            return out.*;
        }

        /// Transforms two `RingElement`s `a` and `b` to their NTT representations,
        /// multiplies them point-wise, and transforms the result back via iNTT.
        ///
        /// Takes O(n log n) complexity.
        pub fn mul(
            self: Self,
            allocator: Allocator,
            a: *Element,
            b: *Element,
        ) !Element {
            const psi_powers_rev = try allocator.alloc(F.M.Fe, a.coefficients.items.len);
            defer allocator.free(psi_powers_rev);
            self.generatePowers(psi_powers_rev, P);

            try self.nwc_ntt(a, psi_powers_rev);
            try self.nwc_ntt(b, psi_powers_rev);

            var res = try ArrayList(F.M.Fe).initCapacity(allocator, a.coefficients.items.len);
            errdefer res.deinit();
            res.appendNTimesAssumeCapacity(self.m.zero, a.coefficients.items.len);

            for (a.coefficients.items, b.coefficients.items, 0..) |a_coeff, b_coeff, i| {
                res.items[i] = self.m.mul(a_coeff, b_coeff);
            }

            var result = Element{ .coefficients = res };

            // Reuse the same buffer used for forward NTT's psis to store
            // inverse NTT's psi inverses.
            const psi_powers_inv_rev = psi_powers_rev;
            const psi_2n_inv = inv(F, P);
            self.generatePowers(psi_powers_inv_rev, psi_2n_inv);
            try self.nwc_intt(&result, psi_powers_inv_rev);

            return result;
        }

        /// Naive schoolbook polynomial multiplication in the `CyclotomicRing`.
        ///
        /// Takes O(n^2) complexity.
        pub fn naiveMul(
            self: Self,
            allocator: Allocator,
            a: Element,
            b: Element,
        ) !Element {
            const n = a.coefficients.items.len;

            var tmp_coeffs = try std.ArrayList(F.M.Fe).initCapacity(allocator, n * 2);
            defer tmp_coeffs.deinit();
            try tmp_coeffs.appendNTimes(self.m.zero, n * 2);

            var result_coeffs = try std.ArrayList(F.M.Fe).initCapacity(allocator, n);
            errdefer result_coeffs.deinit();
            try result_coeffs.appendNTimes(self.m.zero, n);

            for (0..n) |i| {
                for (0..n) |j| {
                    const product = self.m.mul(a.coefficients.items[i], b.coefficients.items[j]);
                    tmp_coeffs.items[i + j] = self.m.add(tmp_coeffs.items[i + j], product);
                }
            }

            for (0..n) |i| {
                result_coeffs.items[i] = self.m.sub(tmp_coeffs.items[i], tmp_coeffs.items[i + n]);
            }

            return .{ .coefficients = result_coeffs };
        }

        /// Generate powers of ψ in bit-reversed order.
        ///
        /// Expects a pre-allocated slice `powers` to populate the powers generated.
        fn generatePowers(self: Self, powers: []F.M.Fe, multiplicant: F.M.Fe) void {
            powers[0] = self.m.one();
            var prev_power = powers[0];

            for (1..powers.len) |i| {
                const idx = @bitReverse(i) >> @truncate(@bitSizeOf(usize) - std.math.log2(powers.len));
                const next_power = self.m.mul(prev_power, multiplicant);
                powers[idx] = next_power;
                prev_power = next_power;
            }
        }

        /// Represents an `element` in negatively wrapped convolution-based NTT representation
        /// using forward NTT with the Cooley-Tukey butterfly.
        ///
        /// a_hat = NTT^ψ(a) = NTT(ψ * a)
        ///
        /// where omega = {ψ_2n}^2 mod q, and
        /// ψ = (1, {ψ_2n}, {ψ_2n}^2, ..., {ψ_2n}^{n-1})
        pub fn nwc_ntt(self: Self, element: *Element, psis_brv: []const F.M.Fe) !void {
            try self.ct_ntt(element, psis_brv);
        }

        /// Transforms an `element` in the NTT representation back to standard representation
        /// using an inverse NTT with the Gentleman-Sande butterfly.
        ///
        /// a = NTT^{ψ^-1}(a_hat) = NTT(ψ^-1 * a_hat)
        ///
        /// where omega = {ψ_2n}^2 mod q, and
        /// ψ^-1 = (1, {ψ_2n}^-1, {ψ_2n}^-2, ..., {ψ_2n}^-{n-1})
        pub fn nwc_intt(self: Self, element: *Element, psis_inverse_brv: []const F.M.Fe) !void {
            try self.gs_intt(element, psis_inverse_brv);

            // Scale each coefficient by n^-1
            const n_inv = inv(F, F.M.Fe.fromPrimitive(F.T, self.m, @intCast(element.coefficients.items.len)) catch unreachable);
            for (element.coefficients.items) |*coeff| coeff.* = self.m.mul(coeff.*, n_inv);
        }

        /// A Decimation-In-Time (DIT) NTT implementation based on the Cooley-Tukey butterfly operation.
        ///
        /// Expects `element` in the natural order, produces outputs in the bit-reversed order.
        /// Expects `psis` to be a precomputed table storing powers of psi in bit-reversed order,
        /// since this implementation traverses the `psis` in order.
        ///
        /// The Cooley-Tukey butterfly:
        ///   A = a + ωb mod q
        ///   B = a - ωb mod q
        ///
        /// Reference: Algorithm 1 in https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/RLWE-1.pdf
        fn ct_ntt(self: Self, element: *Element, psis: []const F.M.Fe) !void {
            const n = element.coefficients.items.len;

            var t: usize = n;
            var m: usize = 1;
            while (m < n) : (m *= 2) {
                t /= 2;

                for (0..m) |i| {
                    const j_1 = 2 * i * t;
                    const j_2 = j_1 + t - 1;
                    const s = psis[m + i];
                    for (j_1..j_2 + 1) |j| {
                        const u = element.coefficients.items[j];
                        const v = self.m.mul(element.coefficients.items[j + t], s);

                        element.coefficients.items[j] = self.m.add(u, v);
                        element.coefficients.items[j + t] = self.m.sub(u, v);
                    }
                }
            }
        }

        /// A Decimation-In-Frequency (DIF) NTT implementation based on the Gentleman-Sande butterfly operation.
        ///
        /// Expects `element` in the bit-reversed order, produces outputs in the natural order.
        /// Expects `psis_inverse` to be a precomputed table storing powers of psi in bit-reversed order,
        /// since this implementation traverses `psis_inverse` in order.
        ///
        /// The Gentleman-Sande butterfly:
        ///   a = A + B mod q
        ///   b = ω(A - B) mod q
        ///
        /// Reference: Algorithm 2 in https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/RLWE-1.pdf
        fn gs_intt(self: Self, element: *Element, psis_inverse: []const F.M.Fe) !void {
            const n = element.coefficients.items.len;

            var t: usize = 1;
            var m: usize = n;
            while (m > 1) : (m /= 2) {
                var j_1: usize = 0;
                const h = m / 2;
                for (0..h) |i| {
                    const j_2 = j_1 + t - 1;
                    const s = psis_inverse[h + i];
                    for (j_1..j_2 + 1) |j| {
                        const u = element.coefficients.items[j];
                        const v = element.coefficients.items[j + t];

                        element.coefficients.items[j] = self.m.add(u, v);
                        element.coefficients.items[j + t] = self.m.mul(self.m.sub(u, v), s);
                    }
                    j_1 += 2 * t;
                }
                t *= 2;
            }
        }
    };
}

fn test_ring_addition(
    comptime F: PrimeField,
    R: type,
    ring_coefficients_a: []F.T,
    ring_coefficients_b: []F.T,
    ring_coefficients_expected: []F.T,
) !void {
    const ring = R.init();
    const expected = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_expected);
    defer expected.deinit();
    var a = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_a);
    var b = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_b);

    const got = try ring.add(&a, &b);
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
    const P = comptime try M.Fe.fromPrimitive(u8, m, try find2NPrimitiveRoot(F, D));
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
    r: type,
    comptime F: PrimeField,
    ring_coefficients_a: []F.T,
    ring_coefficients_b: []F.T,
    ring_coefficients_expected: []F.T,
) !void {
    const ring = r.init();
    const expected = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_expected);
    defer expected.deinit();

    var a = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_a);
    defer a.deinit();
    var b = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_b);
    defer b.deinit();

    // Use naiveMul operation on the ring with element parameters
    const got = try ring.naiveMul(std.testing.allocator, a, b);
    defer got.deinit();
    try std.testing.expectEqualSlices(F.M.Fe, expected.coefficients.items, got.coefficients.items);

    // Make copies for the NTT-based mul which modifies inputs
    var a_copy = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_a);
    defer a_copy.deinit();
    var b_copy = try ring.elementFromSlice(std.testing.allocator, ring_coefficients_b);
    defer b_copy.deinit();

    // Use mul operation on the ring with element parameters
    const got_2 = try ring.mul(std.testing.allocator, &a_copy, &b_copy);
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
    const P = comptime try M.Fe.fromPrimitive(u8, m, try find2NPrimitiveRoot(F, D));
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
    const P = comptime try M.Fe.fromPrimitive(T, m, try find2NPrimitiveRoot(F, D));
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

test "field element inverse" {
    const M = ff.Modulus(8);
    const F = PrimeField{ .M = M, .T = u8, .q = 17 };

    const m = F.M.fromPrimitive(F.T, F.q) catch unreachable;

    // Test inverses of all non-zero elements
    for (1..17) |i| {
        const a = F.M.Fe.fromPrimitive(F.T, m, @intCast(i)) catch unreachable;
        const a_inv = inv(F, a);
        const prod = m.mul(a, a_inv);
        try std.testing.expectEqual(m.one(), prod);
    }

    // Test specific known inverses
    const test_cases = [_]struct { actual: u8, expected: u8 }{
        .{ .actual = 2, .expected = 9 }, // 2 * 9 = 18 ≡ 1 mod 17
        .{ .actual = 3, .expected = 6 }, // 3 * 6 = 18 ≡ 1 mod 17
        .{ .actual = 4, .expected = 13 }, // 4 * 13 = 52 ≡ 1 mod 17
        .{ .actual = 5, .expected = 7 }, // 5 * 7 = 35 ≡ 1 mod 17
        .{ .actual = 6, .expected = 3 }, // 6 * 3 = 18 ≡ 1 mod 17
        .{ .actual = 7, .expected = 5 }, // 7 * 5 = 35 ≡ 1 mod 17
        .{ .actual = 8, .expected = 15 }, // 8 * 15 = 120 ≡ 1 mod 17
        .{ .actual = 9, .expected = 2 }, // 9 * 2 = 18 ≡ 1 mod 17
    };

    for (test_cases) |case| {
        const a = F.M.Fe.fromPrimitive(F.T, m, case.actual) catch unreachable;
        const a_inv = inv(F, a);
        const expected = F.M.Fe.fromPrimitive(F.T, m, case.expected) catch unreachable;
        try std.testing.expectEqual(expected, a_inv);
    }
}

test "primitive root finding" {
    const M = ff.Modulus(32);
    const D = 8;
    const q = 17;
    const F = PrimeField{ .M = M, .T = u32, .q = q };

    const root = try find2NPrimitiveRoot(F, D);

    const m = F.M.fromPrimitive(F.T, F.q) catch unreachable;
    const root_fe = F.M.Fe.fromPrimitive(F.T, m, root) catch unreachable;

    const d = F.M.Fe.fromPrimitive(F.T, m, D) catch unreachable;
    const powered = try m.pow(root_fe, d);
    // Check that root^D ≡ -1 (mod q)
    const neg_one = m.sub(m.zero, m.one());
    try std.testing.expect(powered.eql(neg_one));

    // Check that root^(2*D) ≡ 1 (mod q)
    const two = F.M.Fe.fromPrimitive(F.T, m, 2) catch unreachable;
    const d2 = m.mul(d, two);
    const powered_2d = try m.pow(root_fe, d2);
    try std.testing.expect(powered_2d.eql(m.one()));
}

const std = @import("std");

const ArrayList = std.ArrayList;
const Allocator = std.mem.Allocator;

const ff = std.crypto.ff;

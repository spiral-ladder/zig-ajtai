const PrimeField = @This();

/// The `std.crypto.ff.Modulus` type.
M: type,
/// The integer type used to represent the field.
T: type,
/// The actual modulus `q` used in the `CyclotomicRing`.
q: comptime_int,

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

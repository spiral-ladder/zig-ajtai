pub fn Ajtai(
    Ring: type,
    K: comptime_int,
    M: comptime_int,
) type {
    const Commitment = struct {
        const Self = @This();

        inner: [K]Ring.Element,

        fn deinit(self: Self) void {
            for (0..K) |k| self.inner[k].deinit();
        }
    };

    const RandomMatrix = struct {
        const Self = @This();

        /// The matrix is represented in memory in an array, instead of a 2D array `[K][M]Ring.Element`.
        inner: [K * M]Ring.Element,

        fn deinit(self: Self) void {
            for (0..K) |k|
                for (0..M) |m|
                    self.inner[(k * M) + m].deinit();
        }
    };

    return struct {
        /// Creates a random K×M matrix where each entry is a ring element
        /// with random coefficients. This matrix will be used to compute
        /// commitments.
        ///
        /// Allocates and returns a new `RandomMatrix` instance with randomly generated parameters.
        pub fn setup(
            allocator: Allocator,
        ) !RandomMatrix {
            const r = Ring.init();
            const max_fe = r.m.sub(r.m.zero, r.m.one());
            const max = try max_fe.toPrimitive(Ring.T);
            var matrix: [K * M]Ring.Element = undefined;

            var prng = std.Random.DefaultPrng.init(blk: {
                var seed: u64 = undefined;
                try std.posix.getrandom(std.mem.asBytes(&seed));
                break :blk seed;
            });
            const random = prng.random();
            for (0..K) |k| {
                var coefficients: [M]Ring.T = [_]Ring.T{0} ** M;
                for (&coefficients) |*c| c.* = random.intRangeAtMost(Ring.T, 0, max);
                for (0..M) |m| matrix[k * M + m] = try r.elementFromSlice(allocator, &coefficients);
            }

            return .{ .inner = matrix };
        }

        /// Commits to a `message` using a public `matrix` previously generated with `setup`.
        pub fn commit(
            allocator: Allocator,
            matrix: *RandomMatrix,
            message: *[M]Ring.Element,
        ) !Commitment {
            const r = Ring.init();
            var commitment: [K]Ring.Element = undefined;
            var slice: [K]Ring.T = [_]Ring.T{0} ** K;
            for (0..K) |k| commitment[k] = try r.elementFromSlice(allocator, &slice);

            for (0..K) |k| {
                for (0..M) |m| {
                    var mul = try r.mul(allocator, &matrix.inner[k * M + m], &message[m]);
                    commitment[k] = try r.add(&commitment[k], &mul);
                }
            }

            return .{ .inner = commitment };
        }
    };
}

test "setup and commit" {
    const q = 17;
    const T = u8;
    const F = PrimeField{ .M = ff.Modulus(@bitSizeOf(T)), .T = T, .q = q };
    const D = 8;
    const E = 8;
    const K = 16;
    const M = 16;
    const allocator = std.testing.allocator;
    const m = comptime blk: {
        @setEvalBranchQuota(100_000);
        break :blk F.M.fromPrimitive(T, q) catch unreachable;
    };
    const P = comptime try F.M.Fe.fromPrimitive(T, m, try findPrimitiveRoot(F, D));
    const Ring = CyclotomicRing(.Standard, D, E, F, P);
    const ring = Ring.init();

    // Setup parameters for Ajtai
    const ajtai = Ajtai(Ring, K, M);

    // Setup a K x M matrix as the commitment key
    var matrix = try ajtai.setup(allocator);
    defer matrix.deinit();

    // Prepare random message
    var message: [M]Ring.Element = undefined;
    defer for (0..M) |i| message[i].deinit();
    for (0..M) |i| {
        var coefficients: [M]T = [_]T{10} ** M;
        message[i] = try ring.elementFromSlice(std.testing.allocator, &coefficients);
    }

    // Commit
    const commitment = try ajtai.commit(allocator, &matrix, &message);
    defer commitment.deinit();
}

const PrimeField = @import("ring.zig").PrimeField;
const CyclotomicRing = @import("ring.zig").CyclotomicRing;
const RingModuloCfg = @import("ring.zig").RingModuloCfg;
const findPrimitiveRoot = @import("ring.zig").findPrimitiveRoot;

const std = @import("std");

const ArrayList = std.ArrayList;
const Allocator = std.mem.Allocator;

const ff = std.crypto.ff;

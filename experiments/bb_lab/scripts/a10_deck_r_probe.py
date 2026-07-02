"""A10 probe: is the homotopy (R) (sigma_* = id on H1(cover)) automatic?

For a BB pair (A, B) on the cover group Z_l x Z_m with deck sigma = x^(l/2)
(free Z2 cover doubling x), this script computes, over F2:

  - k_cover  = dim H1(cover)          (= 2 * dim R~/(A,B))
  - k_base   = dim H1(base)           (base group Z_(l/2) x Z_m, same polys)
  - dim eps*H1(cover)  where eps = 1 + sigma   ((R) holds  <=>  this is 0)
  - membership: 1 + x^(l/2) in ideal (A, B) of F2[Z_l x Z_m]
                (<=> vec(1+s) in im d1, since im d1 = {PA + QB})

Predictions being tested (A10 plan):
  T1 (theorem):    membership  =>  (R)          (Koszul H1 killed by (A,B))
  C1 (counting):   membership <=>  k_cover = k_base
  R* (conjecture): (R)        <=>  membership   (the open (=>) direction)
  Dead-block construction: common character root of all sector components
    of A and B  =>  (R) FAILS (headline: (R) not automatic).

Pure stdlib; matrices as lists of int bitmasks (rows = F2 vectors).
Run: uv run python scripts/a10_deck_r_probe.py   (from experiments/bb_lab)
"""


def rank_of(rows):
    """Rank over F2 of a list of int bitmask rows (destructive on a copy)."""
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        if r:
            basis.append(r)
            basis.sort(reverse=True)
    return len(basis)


def rref_basis(rows):
    """Reduced basis (list of pivoted int rows) of the row space."""
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        if r:
            basis.append(r)
            basis.sort(reverse=True)
    return basis


def in_span(v, basis):
    for b in basis:
        v = min(v, v ^ b)
    return v == 0


class BBGroup:
    def __init__(self, l, m):
        self.l, self.m, self.n = l, m, l * m

    def idx(self, i, j):
        return (i % self.l) * self.m + (j % self.m)

    def mono_perm(self, a, b):
        """Multiplication by x^a y^b as an index permutation."""
        return [self.idx(i + a, j + b) for i in range(self.l) for j in range(self.m)]

    def poly_matrix(self, poly):
        """Multiplication-by-poly matrix, as n columns (int bitmasks over rows)."""
        cols = [0] * self.n
        for (a, b) in poly:
            perm = self.mono_perm(a, b)
            for src in range(self.n):
                cols[src] ^= 1 << perm[src]
        return cols  # cols[src] = image of basis vector src


def bb_data(l, m, A, B):
    """Return (k, dim_eps_H1, membership) for the BB complex on Z_l x Z_m.

    d2 : R -> R^2, h |-> (B h, A h);  d1 : R^2 -> R, (f,g) |-> A f + B g.
    eps/membership fields are None when l is odd (no x-doubling deck).
    """
    G = BBGroup(l, m)
    n = G.n
    MA, MB = G.poly_matrix(A), G.poly_matrix(B)

    # d1 as a (2n x n)-column map: columns indexed by C1-basis, values in C0.
    d1_cols = MA + MB  # first n columns act by A (f-part), next n by B (g-part)
    # d2 columns: h-basis vector -> (B h, A h) stacked into 2n bits.
    d2_cols = [MB[src] | (MA[src] << n) for src in range(n)]

    # ker d1: solve d1 * v = 0 by eliminating the transposed system.
    # Build rows (v-coordinates augmented) via standard kernel extraction.
    # Represent each C1 basis vector's image; kernel = null space of the
    # n x 2n matrix with columns d1_cols.
    # Transpose to rows over 2n-bit vectors:
    rows = []
    for r in range(n):
        bits = 0
        for c in range(2 * n):
            if (d1_cols[c] >> r) & 1:
                bits |= 1 << c
        rows.append(bits)
    # kernel of the row system {x : rows . x = 0}: eliminate with tracking.
    # Standard trick: augment identity on 2n coords and row-reduce columns.
    pivots = {}
    for c in range(2 * n):
        v = 0
        for r in range(n):
            if (rows[r] >> c) & 1:
                v |= 1 << r
        # reduce v against pivot columns, tracking combination
        comb = 1 << c
        for pc, (pv, pcomb) in pivots.items():
            low = pv & -pv
            if v & low:
                v ^= pv
                comb ^= pcomb
        if v:
            pivots[c] = (v, comb)
    ker_basis = []
    seen_cols = set(pivots)
    # free columns give kernel vectors: comb of a fully-reduced zero column
    pivots2 = {}
    ker_basis = []
    for c in range(2 * n):
        v = 0
        for r in range(n):
            if (rows[r] >> c) & 1:
                v |= 1 << r
        comb = 1 << c
        for pv, pcomb in pivots2.values():
            low = pv & -pv
            if v & low:
                v ^= pv
                comb ^= pcomb
        if v:
            pivots2[len(pivots2)] = (v, comb)
        else:
            ker_basis.append(comb)

    im2 = rref_basis(list(d2_cols))
    k = len(ker_basis) - len(im2)

    dim_eps_h1 = None
    member = None
    if l % 2 == 0:
        s = l // 2
        perm = G.mono_perm(s, 0)

        def sigma1(v):
            out = 0
            for src in range(n):
                if (v >> src) & 1:
                    out |= 1 << perm[src]
                if (v >> (n + src)) & 1:
                    out |= 1 << (n + perm[src])
            return out

        eps_ker = [v ^ sigma1(v) for v in ker_basis]
        dim_eps_h1 = rank_of(im2 + eps_ker) - len(im2)

        # membership: vec(1 + x^s) in column space of [MA | MB]
        target = (1 << G.idx(0, 0)) ^ (1 << G.idx(s, 0))
        colspace = rref_basis(MA + MB)
        member = in_span(target, colspace)

    return k, dim_eps_h1, member


def case(name, l, m, A, B):
    kc, deps, mem = bb_data(l, m, A, B)
    kb, _, _ = bb_data(l // 2, m, [(a % (l // 2), b) for (a, b) in A],
                       [(a % (l // 2), b) for (a, b) in B])
    r_holds = (deps == 0)
    print(f"{name:34s} k_cover={kc:3d} k_base={kb:3d} "
          f"dim(eps*H1)={deps:3d} (R):{'HOLDS' if r_holds else 'FAILS'} "
          f"1+s in (A,B): {'yes' if mem else 'NO'}")
    # consistency checks: T1 and C1
    assert (not mem) or r_holds, "T1 violated: membership without (R)!"
    assert mem == (kc == kb), "C1 violated: membership <-> k preserved!"
    return r_holds, mem, kc, kb


print("== A10 deck-homotopy (R) probe — cover Z_l x Z_m, deck s = x^(l/2) ==")
# controls (expected: (R) HOLDS, k preserved, membership yes)
case("toric-ish Z6xZ3 (1+x, 1+y)", 6, 3, [(0, 0), (1, 0)], [(0, 0), (0, 1)])
case("gross Z12xZ6 x-doubling", 12, 6,
     [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)])
case("pair72 Z6xZ6 x-doubling", 6, 6,
     [(2, 0), (0, 1), (0, 3)], [(0, 0), (1, 0), (0, 2)])
# dead-block counterexamples (expected: (R) FAILS, k jumps, no membership)
case("CE1 Z6xZ3 A=1+y+y2 B=x2*A", 6, 3,
     [(0, 0), (0, 1), (0, 2)], [(2, 0), (2, 1), (2, 2)])
case("CE2 Z6xZ3 A=1+y+y2 B=1+x2+x4", 6, 3,
     [(0, 0), (0, 1), (0, 2)], [(0, 0), (2, 0), (4, 0)])
print("all T1/C1 consistency assertions passed")

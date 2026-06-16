"""A3 / Track 1.1 Entry 27 — adversarial re-review of Entries 16-26
(the d(gross) = 12 chain: safe-sector reduction, (R), flux, (M-im)).

INDEPENDENT re-implementation of every load-bearing machine check behind
Entries 16-26.  Deliberately uses a different encoding path from the lab's
scripts (`bb_lab.*` is NOT imported; no a3_* code is reused):

  - own group indexing: y-major idx(x, y) = y*XN + x (lab: x-major
    row-major x*m + y) — catches transposition/convention bugs;
  - own F2 linear algebra on Python int bitmasks (top-bit-pivot solver
    with combination tracking), vs the lab's numpy Gaussian elimination;
  - own crossing predicate: a step from x with x-advance s crosses cut j
    iff (j - x - 1) mod 6 < s  (provably equivalent to, but spelled
    differently from, the lab's (x - j) % 6 + s >= 6);
  - own CRT frame: slot s = 2*(x%2) + (y%2) (bit roles swapped vs the
    lab), cell index 3*ty + tx, and the CONJUGATE character-orbit reps
    (c, d) in {(0,0), (0,2), (2,0), (2,2), (2,1)} (the lab uses
    (0,1), (1,0), (1,1), (1,2)) — every F4 constant here is the
    Frobenius conjugate of the lab's, so agreement of all structural
    facts is a nontrivial frame-transport check;
  - F4 multiplication built at runtime from theta^2 = theta + 1, not a
    hardcoded table;
  - boundary/image membership via direct solve, the weight-8/10 census
    via own meet-in-middle (numpy int64 + bitwise_count kernel scans +
    syndrome hash-joins), vs the lab's numpy row-ops + packed popcounts.

Frame notes for comparing against the lab's printed constants: with the
conjugate reps, Ahat_1 = X + w^2 Y (lab: X + w Y), Bhat_4 = w^2 Ahat_4
(lab: w), D1 reads Y u1 = w Y u2 (lab: w^2), etc.  All counts, censuses,
floors, table multisets, achiever counts and kill verdicts must agree
exactly — those are frame-independent.

Sections (each check prints PASS/FAIL; summary at the end):

  AV1  foundations: base/cover matrices; the cover block form
       [[nc_j, c_j], [c_j, nc_j]] for H_X AND the d2-split for every
       cut; the crossing-set bookkeeping (A's x^3 crosses from window
       cols {3,4,5}; B's x from {5}, x^2 from {4,5}); d2c_0 column
       formula (L = x P5 + x^2 (P4+P5), R = x^3 (P3+P4+P5)).
  AV2  Entry 16: weight-6 census/splits/orbits/classes; all 84 weight-6
       logicals UNREACHABLE (slice empty, every cut); ker(delta) =
       im(Delta) as class sets (64 = 64, all cuts); Delta injective;
       slice algebra spot-checks (lift to cover cycle, weight identity);
       coker d1 = 6 with the per-CRT-component dims (0,0,0,2,4);
       ker d2: dim 6, weight enumerator {16:9, 18:48, 24:6}, comps
       {0,1,2} of every zeta vanish.
  AV3  Entry 17: the homotopy identities; d2((1+x^2) B v_L) = v + sigma v
       on a FULL basis of ker H_X^cov (78); tau(p(v)) = (1+sigma)v;
       base degeneration; the 5 translation orbits of ker d2 \ 0
       (swap-closed); |d2c_j zeta| tables; all-84 weight-6 fluxes
       nonzero; the upper-bound witness tau(u*) (weight 12, cover cycle,
       NOT a boundary).
  AV4  Entry 18: no-double-wrap d1c_j d2c_j = 0, d1nc_j d2nc_j = 0,
       d1nc d2c = d1c d2nc as matrix identities for all 6 cuts; flux
       well-defined on classes (xi^T d1c d2 = 0); ker(flux) = im(Delta)
       as class sets; the M8 pins ({3,4}, {4}, {3,4}, {4}, {3}).
  AV5  Entries 19/22: class transport class(T zeta) = T class(zeta)
       (all 63 x 36, exact); column/row evenness + the column relation;
       off0 diagonal — and the SHARPER fact found in this review:
       off0 = off2 = 0 IDENTICALLY (from Y^2 = 0; see Entry 27 log);
       block parities; value bijection + E <= 2 rigidity; rho-locks
       (rho_i^2 = 0, im rho_i = F4 rho_i + F4 XY, 16 elements);
       c1 = c2 = 0 on all 63 zeta; Gamma_3 / Gamma_4 parametrizations;
       the 66-fibre +4 gap (informational); confined floors
       10/10/10/12/12.
  AV6  Entries 23/24: M1 census {0:1, 1:9, 2:36, 3:55, 4:27}; the HAND
       RULES (alive-count + T-classifier) reproduce M1 and M2 on all
       128 cells each; M2 = M1 o (Frob on comp 4); 18 orbits; the
       character identities; the spine C-tables by brute force: floors,
       value multisets, floor-10 cell counts (4/14/12), wt-24 block
       minima = 6 at every cell (both blocks); translation stabilizers.
  AV7  Entry 25: independent achiever enumeration at the floor-10
       orbits (counts 48/48/22) and the rho-link kills: every achiever
       fails a link (with the lab's exception structure: 2 achievers in
       wt-18b fail exactly one).
  AV8  Entry 21 (and the (M-im) endpoint, independently): complete own
       census of weight-6/8/10 1-cycles (120 / 990 / 13464), boundary
       counts (36 / 0 / 216), flux-silent non-boundaries = ZERO, split
       and orbit counts.
  AV9  Entry 26: the unpinnedness chains in transform coordinates
       (u-relations, R1/R2, D1, the reduced identity, endpoints), all
       63 zeta; the comp-2 collapse v_i = 0 (this review's one-line
       sharpening).

Computation may REFUTE but never PROVE: everything here is a hunt for a
counterexample to an intermediate claim of the hand proofs.  All-PASS
means the hunt failed, not that the proofs are machine-verified.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, product

import numpy as np

RESULTS: list[tuple[str, bool]] = []


def check(name: str, ok: bool):
    RESULTS.append((name, bool(ok)))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")


# =========================================================================
# own F2 linear algebra (int bitmasks, top-bit pivots, combo tracking)
# =========================================================================
class F2Solver:
    """Column-space solver for M x = b, M given as a list of column ints."""

    def __init__(self, cols):
        self.ncols = len(cols)
        self.piv = {}              # pivot bit -> (vec, combo)
        self.null = []             # combos spanning the null space
        for i, v in enumerate(cols):
            c = 1 << i
            v, c = self._reduce(v, c)
            if v:
                self.piv[v.bit_length() - 1] = (v, c)
            else:
                self.null.append(c)

    def _reduce(self, v, c):
        while v:
            p = v.bit_length() - 1
            if p not in self.piv:
                break
            bv, bc = self.piv[p]
            v ^= bv
            c ^= bc
        return v, c

    def solve(self, b):
        v, c = self._reduce(b, 0)
        return None if v else c

    @property
    def rank(self):
        return len(self.piv)


def span(vecs):
    """All 2^k combinations of the basis list `vecs` (ints)."""
    out = [0]
    for v in vecs:
        out += [x ^ v for x in out]
    return out


def popcount(x):
    return bin(x).count("1")


# =========================================================================
# groups, polynomials, matrices  (y-major indexing!)
# =========================================================================
BX, BY = 6, 6
N = 36


def bidx(x, y):
    return (y % BY) * BX + (x % BX)


BCELLS = [(x, y) for y in range(BY) for x in range(BX)]
A_SUPP = [(3, 0), (0, 1), (0, 2)]
B_SUPP = [(0, 3), (1, 0), (2, 0)]


def poly_col(supp, g):
    """Column of M_P at group element g: bits at g + p."""
    m = 0
    for (px, py) in supp:
        m |= 1 << bidx(g[0] + px, g[1] + py)
    return m


# H_X = (M_A | M_B): 72 columns of 36-bit ints
HX_COLS = [poly_col(A_SUPP, g) for g in BCELLS] + \
          [poly_col(B_SUPP, g) for g in BCELLS]
# d2 = H_Z^T: 36 columns of 72-bit ints (left block B-steps, right A-steps)
D2_COLS = [poly_col(B_SUPP, g) | (poly_col(A_SUPP, g) << N) for g in BCELLS]
# H_Z = (M_B^T | M_A^T): 72 columns of 36-bit ints (col h: checks h - p)
HZ_COLS = [0] * 72
for i, g in enumerate(BCELLS):
    m = 0
    for (px, py) in B_SUPP:
        m |= 1 << bidx(g[0] - px, g[1] - py)
    HZ_COLS[i] = m
    m = 0
    for (px, py) in A_SUPP:
        m |= 1 << bidx(g[0] - px, g[1] - py)
    HZ_COLS[N + i] = m


def cross(x, s, j):
    """Does an x-step of size s from column x cross cut j?  (own form;
    equivalent to the lab's (x - j) % 6 + s >= 6.)"""
    return ((j - x - 1) % 6) < s


def d1_split(j):
    """(d1nc_j, d1c_j) as column lists (36-bit ints)."""
    nc = [0] * 72
    cc = [0] * 72
    for blk, supp in ((0, A_SUPP), (1, B_SUPP)):
        for i, g in enumerate(BCELLS):
            col = blk * N + i
            for (px, py) in supp:
                bit = 1 << bidx(g[0] + px, g[1] + py)
                if cross(g[0], px, j):
                    cc[col] |= bit
                else:
                    nc[col] |= bit
    return nc, cc


def d2_split(j):
    """(d2nc_j, d2c_j) as column lists (72-bit ints)."""
    nc = [0] * N
    cc = [0] * N
    for i, g in enumerate(BCELLS):
        for blk, supp in ((0, B_SUPP), (1, A_SUPP)):
            for (px, py) in supp:
                bit = 1 << (blk * N + bidx(g[0] + px, g[1] + py))
                if cross(g[0], px, j):
                    cc[i] |= bit
                else:
                    nc[i] |= bit
    return nc, cc


D1S = {j: d1_split(j) for j in range(6)}
D2S = {j: d2_split(j) for j in range(6)}


def apply_cols(cols, vec):
    out = 0
    while vec:
        b = vec & -vec
        out ^= cols[b.bit_length() - 1]
        vec ^= b
    return out


def vec_weight_split(w):
    return popcount(w & ((1 << N) - 1)), popcount(w >> N)


def translate36(v, dx, dy):
    out = 0
    while v:
        b = v & -v
        i = b.bit_length() - 1
        out |= 1 << bidx(i % BX + dx, i // BX + dy)
        v ^= b
    return out


def translate72(w, dx, dy):
    return translate36(w & ((1 << N) - 1), dx, dy) | \
        (translate36(w >> N, dx, dy) << N)


# cover (Z12 x Z6), y-major
CX = 12
NC = 72


def cidx(x, y):
    return (y % 6) * CX + (x % CX)


CCELLS = [(x, y) for y in range(6) for x in range(CX)]
HXC_COLS = [0] * 144
D2C_COV_COLS = [0] * NC
for i, g in enumerate(CCELLS):
    m = 0
    for (px, py) in A_SUPP:
        m |= 1 << cidx(g[0] + px, g[1] + py)
    HXC_COLS[i] = m
    ma = m
    m = 0
    for (px, py) in B_SUPP:
        m |= 1 << cidx(g[0] + px, g[1] + py)
    HXC_COLS[NC + i] = m
    D2C_COV_COLS[i] = m | (ma << NC)   # d2^cov face g -> (B g, A g)

SOLVE_HX = F2Solver(HX_COLS)
SOLVE_D2 = F2Solver(D2_COLS)
SOLVE_HXC = F2Solver(HXC_COLS)
SOLVE_D2COV = F2Solver(D2C_COV_COLS)

KER_HX = SOLVE_HX.null                # base 1-cycles (dim 42)
KER_D2 = SOLVE_D2.null                # base 2-cycles  (dim 6)
KER_HXC = SOLVE_HXC.null              # cover 1-cycles (dim 78)
KER_HZ = F2Solver(HZ_COLS).null       # X-side cycles  (dim 42)

# left null space of H_X (flux functionals xi): nullspace of H_X^T
HX_ROWS = [0] * N
for c, col in enumerate(HX_COLS):
    v = col
    while v:
        b = v & -v
        HX_ROWS[b.bit_length() - 1] |= 1 << c
        v ^= b
K0 = F2Solver(HX_ROWS).null           # 6 functionals, 36-bit ints

# class functionals: 12 elements of ker H_Z independent of rowspace H_X
HZ_ROWS = [0] * N
for c, col in enumerate(HZ_COLS):
    v = col
    while v:
        b = v & -v
        HZ_ROWS[b.bit_length() - 1] |= 1 << c
        v ^= b
_acc = F2Solver([])
for r in HX_ROWS:
    v, c = _acc._reduce(r, 0)
    if v:
        _acc.piv[v.bit_length() - 1] = (v, c)
CLASS_FUN = []
for u in KER_HZ:
    v, c = _acc._reduce(u, 0)
    if v:
        _acc.piv[v.bit_length() - 1] = (v, c)
        CLASS_FUN.append(u)


def cls(w):
    return tuple(popcount(u & w) & 1 for u in CLASS_FUN)


# H1 basis on the Z side: 12 cycles independent mod im d2
_accz = F2Solver([])
for col_idx in range(N):
    # rows of B1 = columns of d2 viewed as vectors
    v, c = _accz._reduce(D2_COLS[col_idx], 0)
    if v:
        _accz.piv[v.bit_length() - 1] = (v, c)
H1_BASIS = []
for u in KER_HX:
    v, c = _accz._reduce(u, 0)
    if v:
        _accz.piv[v.bit_length() - 1] = (v, c)
        H1_BASIS.append(u)

print("=== AV1: foundations — block forms and crossing bookkeeping ===")
check("dim ker H_X = 42, dim ker d2 = 6, dim ker H_X^cov = 78, "
      "dim ker H_Z = 42",
      (len(KER_HX), len(KER_D2), len(KER_HXC), len(KER_HZ))
      == (42, 6, 78, 42))
check("dim coker d1 = 6 (flux functionals), H1 basis = 12, class fun = 12",
      (len(K0), len(H1_BASIS), len(CLASS_FUN)) == (6, 12, 12))

# d1nc + d1c = H_X, d2nc + d2c = d2, every cut; crossing sets as stated
ok = all(all(D1S[j][0][c] ^ D1S[j][1][c] == HX_COLS[c] for c in range(72))
         and all(D2S[j][0][c] ^ D2S[j][1][c] == D2_COLS[c] for c in range(N))
         for j in range(6))
check("d1nc_j + d1c_j = H_X and d2nc_j + d2c_j = d2 for all 6 cuts", ok)

ok = True
for j in range(6):
    for x in range(6):
        r = (x - j) % 6
        ok &= cross(x, 3, j) == (r >= 3)       # A's x^3: window cols 3,4,5
        ok &= cross(x, 1, j) == (r == 5)       # B's x: col 5
        ok &= cross(x, 2, j) == (r >= 4)       # B's x^2: cols 4, 5
        ok &= not cross(x, 0, j)
check("crossing sets: x^3 from {3,4,5}, x from {5}, x^2 from {4,5} "
      "(window-relative, all cuts)", ok)

# d2c_0 column formula on all 36 faces
ok = True
for i, g in enumerate(BCELLS):
    L = 0
    R = 0
    if g[0] % 6 == 5:
        L ^= 1 << bidx(g[0] + 1, g[1])
    if g[0] % 6 in (4, 5):
        L ^= 1 << bidx(g[0] + 2, g[1])
    if g[0] % 6 in (3, 4, 5):
        R ^= 1 << bidx(g[0] + 3, g[1])
    ok &= D2S[0][1][i] == (L | (R << N))
check("d2c_0 = (x P5 + x^2 (P4+P5) | x^3 (P3+P4+P5)) on every face", ok)

# cover block form for H_X^cov and d2^cov, every cut
ok_bf = True
for j in range(6):
    d1nc, d1c = D1S[j]
    d2nc, d2c = D2S[j]

    def sheet(x):
        return 0 if (x - j) % 12 < 6 else 1

    cov_of = {}                       # (sheet, x%6, y) -> cover x
    for x in range(12):
        for y in range(6):
            cov_of[(sheet(x), x % 6, y)] = x
    # H_X^cov blocks
    for sc in range(2):
        for sq in range(2):
            ok_blk = True
            for blk in range(2):
                for gi, g in enumerate(BCELLS):
                    xq = cov_of[(sq, g[0], g[1])]
                    col = HXC_COLS[blk * NC + cidx(xq, g[1])]
                    # extract rows living on check-sheet sc
                    ext = 0
                    v = col
                    while v:
                        b = v & -v
                        ci = b.bit_length() - 1
                        cxx, cyy = ci % CX, ci // CX
                        if sheet(cxx) == sc:
                            ext |= 1 << bidx(cxx % 6, cyy)
                        v ^= b
                    ref = (d1nc if sc == sq else d1c)[blk * N + gi]
                    ok_blk &= ext == ref
            ok_bf &= ok_blk
    # d2^cov blocks
    for sc in range(2):
        for sq in range(2):
            for gi, g in enumerate(BCELLS):
                xf = cov_of[(sq, g[0], g[1])]
                col = D2C_COV_COLS[cidx(xf, g[1])]
                ext = 0
                for blk in range(2):
                    v = (col >> (blk * NC)) & ((1 << NC) - 1)
                    while v:
                        b = v & -v
                        qi = b.bit_length() - 1
                        qx, qy = qi % CX, qi // CX
                        if sheet(qx) == sc:
                            ext |= 1 << (blk * N + bidx(qx % 6, qy))
                        v ^= b
                ref = (d2nc if sc == sq else d2c)[gi]
                if ext != ref:
                    ok_bf = False
check("cover block form [[nc_j, c_j],[c_j, nc_j]] for H_X^cov AND d2^cov, "
      "all 6 cuts", ok_bf)


# =========================================================================
print("\n=== AV2: Entry 16 — safe-slice framework, ker delta = im Delta ===")
# weight-6 cycle census by split (meet-in-middle, own implementation)
MA_COLS = HX_COLS[:N]
MB_COLS = HX_COLS[N:]
ANN_A = F2Solver(MA_COLS).null
ANN_B = F2Solver(MB_COLS).null
annA_all = span(ANN_A)
annB_all = span(ANN_B)
wA = Counter(popcount(z) for z in annA_all)
wB = Counter(popcount(z) for z in annB_all)
check("Ann(A), Ann(B) weight enumerators {0:1, 6:36, 8:9, ...} agree and "
      "min weight 6",
      wA == wB and wA[6] == 36 and wA[8] == 9
      and min(w for w in wA if w > 0) == 6)


def syndromes_of(cols, k):
    out = {}
    for T in combinations(range(N), k):
        s = 0
        m = 0
        for i in T:
            s ^= cols[i]
            m |= 1 << i
        out.setdefault(s, []).append(m)
    return out


def census_weight(W):
    """All 1-cycles of total weight W as (maskL, maskR) pairs, by split."""
    out = {}
    SA = {k: syndromes_of(MA_COLS, k) for k in range(0, W + 1)}
    SB = {k: syndromes_of(MB_COLS, k) for k in range(0, W + 1)}
    for a in range(W + 1):
        b = W - a
        found = []
        if a == 0:
            found = [(0, z) for z in annB_all if popcount(z) == W]
        elif b == 0:
            found = [(z, 0) for z in annA_all if popcount(z) == W]
        else:
            common = set(SA[a]) & set(SB[b])
            for s in common:
                for mL in SA[a][s]:
                    for mR in SB[b][s]:
                        found.append((mL, mR))
        if found:
            out[(a, b)] = found
    return out


c6 = census_weight(6)
n6 = sum(len(v) for v in c6.values())
check("weight-6 cycles: 120 with splits (6,0):36, (3,3):48, (0,6):36",
      n6 == 120 and {k: len(v) for k, v in c6.items()}
      == {(6, 0): 36, (3, 3): 48, (0, 6): 36})

all6 = [mL | (mR << N) for v in c6.values() for (mL, mR) in v]
bnd6 = [w for w in all6 if SOLVE_D2.solve(w) is not None]
log6 = [w for w in all6 if SOLVE_D2.solve(w) is None]
check("36 boundaries (hexagons) + 84 logicals among weight-6",
      (len(bnd6), len(log6)) == (36, 84))
check("the 84 weight-6 logicals occupy 84 distinct H1 classes",
      len({cls(w) for w in log6}) == 84)
orb6 = {}
for w in log6:
    key = min((translate72(w, dx, dy) for dx in range(6) for dy in range(6)))
    orb6.setdefault(key, []).append(w)
check("84 logicals: 3 translation orbits, sizes {12, 36, 36}",
      sorted(len(v) for v in orb6.values()) == [12, 36, 36])

# all 84 unreachable: d1 v0 = d1c_j w unsolvable, every cut
ok = all(SOLVE_HX.solve(apply_cols(D1S[j][1], w)) is None
         for w in log6 for j in range(6))
check("ALL 84 weight-6 logicals are UNREACHABLE (slice empty, all 6 cuts)",
      ok)

# ker delta = im Delta as class sets (all cuts) + Delta injective
imD_classes = {}
for j in range(6):
    s = set()
    for zmask in span(KER_D2):
        s.add(cls(apply_cols(D2S[j][1], zmask)))
    imD_classes[j] = frozenset(s)
ok_inj = len(imD_classes[0]) == 64
kerdelta = {}
for j in range(6):
    s = set()
    for hmask in range(4096):
        w = 0
        for i in range(12):
            if (hmask >> i) & 1:
                w ^= H1_BASIS[i]
        if SOLVE_HX.solve(apply_cols(D1S[j][1], w)) is not None:
            s.add(cls(w))
    kerdelta[j] = frozenset(s)
check("im Delta cut-independent, 64 classes (Delta injective)",
      len(set(imD_classes.values())) == 1 and ok_inj)
check("ker delta cut-independent and ker delta == im Delta (64 classes)",
      len(set(kerdelta.values())) == 1 and kerdelta[0] == imD_classes[0])

# slice algebra spot checks: reachable w -> v0 lifts to cover cycle with
# the weight identity |v| = |w| + 2|v0 off supp w|
rng = np.random.default_rng(27)
ok_lift = True
zlist = [z for z in span(KER_D2) if z]
for trial in range(12):
    z = zlist[int(rng.integers(len(zlist)))]
    w = apply_cols(D2S[0][1], z)
    s = apply_cols(D1S[0][1], w)
    v0 = SOLVE_HX.solve(s)
    assert v0 is not None
    # randomize over the kernel
    for i in rng.choice(len(KER_HX), 6, replace=False):
        v0 ^= KER_HX[int(i)]
    v1 = v0 ^ w
    # lift at cut 0: sheet 0 holds window {0..5} = identity embedding
    vcov = 0
    for blk in range(2):
        for sheet, vs in ((0, v0), (1, v1)):
            vv = (vs >> (blk * N)) & ((1 << N) - 1)
            while vv:
                b = vv & -vv
                i = b.bit_length() - 1
                x, y = i % BX, i // BX
                vcov |= 1 << (blk * NC + cidx(x + 6 * sheet, y))
                vv ^= b
    syn = 0
    vv = vcov
    while vv:
        b = vv & -vv
        syn ^= HXC_COLS[b.bit_length() - 1]
        vv ^= b
    off = popcount(v0 & ~w)
    ok_lift &= (syn == 0) and (popcount(vcov)
                               == popcount(w) + 2 * off)
check("slice algebra: v0-solutions lift to cover cycles with "
      "|v| = |w| + 2|v0 off supp w| (12 random)", ok_lift)
# calibration: REACHABLE w (Smith reps) have solvable slices at EVERY cut
ok_cal = all(SOLVE_HX.solve(apply_cols(D1S[j][1],
                                       apply_cols(D2S[0][1], z))) is not None
             for z in zlist[:9] for j in range(6))
check("calibration: Smith reps ARE reachable (slice solvable, all cuts) — "
      "the unreachability test can tell the difference", ok_cal)

# ker d2 structure
wts = Counter(popcount(z) for z in zlist)
check("ker d2 weight enumerator {16:9, 18:48, 24:6}",
      dict(wts) == {16: 9, 18: 48, 24: 6})


# =========================================================================
# own CRT frame (conjugate orbit reps)
# =========================================================================
def f4mul_raw(a, b):
    """F4 as a0 + 2*a1, theta^2 = theta + 1 — computed, not hardcoded."""
    a0, a1 = a & 1, a >> 1
    b0, b1 = b & 1, b >> 1
    hi = a0 * b1 + a1 * b0 + a1 * b1     # theta coefficient
    lo = a0 * b0 + a1 * b1               # theta^2 = theta + 1 folds in
    return (lo & 1) | ((hi & 1) << 1)


F4M = [[f4mul_raw(a, b) for b in range(4)] for a in range(4)]
F4INV = {1: 1, 2: 3, 3: 2}
WP = [1, 2, 3]                            # theta^0, theta^1, theta^2
R5 = {0: (0, 0), 1: (0, 2), 2: (2, 0), 3: (2, 2), 4: (2, 1)}   # CONJUGATE reps


def slot_of(x, y):
    return 2 * (x % 2) + (y % 2)          # bit roles swapped vs the lab


def comp_hat(mask36, j):
    out = [0, 0, 0, 0]
    c, d = R5[j]
    v = mask36
    while v:
        b = v & -v
        i = b.bit_length() - 1
        x, y = i % BX, i // BX
        out[slot_of(x, y)] ^= WP[(c * (x % 3) + d * (y % 3)) % 3]
        v ^= b
    return tuple(out)


def rmul(f, g):
    out = [0, 0, 0, 0]
    for s1 in range(4):
        if f[s1]:
            for s2 in range(4):
                if g[s2]:
                    out[s1 ^ s2] ^= F4M[f[s1]][g[s2]]
    return tuple(out)


def rxor(a, b):
    return tuple(p ^ q for p, q in zip(a, b))


def smul(lam, v):
    return tuple(F4M[lam][p] for p in v)


ALL_F4T = [tuple(t) for t in product(range(4), repeat=4)]
ALL_F2T = [t for t in ALL_F4T if all(c in (0, 1) for c in t)]
AH = {j: comp_hat(poly_col(A_SUPP, (0, 0)), j) for j in range(5)}
BH = {j: comp_hat(poly_col(B_SUPP, (0, 0)), j) for j in range(5)}


def rinv(u):
    return next(t for t in ALL_F4T if rmul(u, t) == (1, 0, 0, 0))


def aug(v):
    a = 0
    for x in v:
        a ^= x
    return a


XYr = rmul(rxor((1, 0, 0, 0), comp_hat(1 << bidx(1, 0), 0)),
           rxor((1, 0, 0, 0), comp_hat(1 << bidx(0, 1), 0)))
# (XY = (1+s_x)(1+s_y); built from actual group elements as a sanity step)
assert XYr == (1, 1, 1, 1)

# layer value table in my frame
WT = np.full((2, 4, 4, 4, 4), -1, np.int8)
for fb in range(512):
    vals = []
    for j, (c, d) in R5.items():
        acc = 0
        for ty in range(3):
            for tx in range(3):
                if (fb >> (3 * ty + tx)) & 1:
                    acc ^= WP[(c * tx + d * ty) % 3]
        vals.append(acc)
    WT[vals[0], vals[1], vals[2], vals[3], vals[4]] = bin(fb).count("1")
M1 = WT.min(axis=1)
M2 = WT.min(axis=2)


# =========================================================================
print("\n=== AV3: Entry 17 — (R), orbits, fluxes, the upper-bound witness ===")


def conv_cover(s1, s2):
    out = set()
    for a in s1:
        for b in s2:
            c = ((a[0] + b[0]) % 12, (a[1] + b[1]) % 6)
            if c in out:
                out.remove(c)
            else:
                out.add(c)
    return out


Bset = set(B_SUPP)
B2 = conv_cover(Bset, Bset)
check("over F2[Z12 x Z6]: B^2 = 1 + x^2 + x^4",
      B2 == {(0, 0), (2, 0), (4, 0)})
eps = conv_cover({(0, 0), (2, 0)}, B2)
check("(1 + x^2) B^2 = 1 + x^6", eps == {(0, 0), (6, 0)})
B2b = {((a[0] % 6), a[1]) for a in []}  # base: recompute directly
bb = set()
for a in B_SUPP:
    for b in B_SUPP:
        c = ((a[0] + b[0]) % 6, (a[1] + b[1]) % 6)
        bb ^= {c}
ee = set()
for m in [(0, 0), (2, 0)]:
    for b in bb:
        c = ((m[0] + b[0]) % 6, (m[1] + b[1]) % 6)
        ee ^= {c}
check("over the base ring: (1 + x^2) B^2 = 0 (degeneration)", ee == set())

# multiplication-by-(1+x^2)B and by-x^6 on F2[Gc], as column maps
TB_COLS = [0] * NC
SIG_COLS = [0] * NC
mset = conv_cover({(0, 0), (2, 0)}, Bset)
for i, g in enumerate(CCELLS):
    m = 0
    for (px, py) in mset:
        m ^= 1 << cidx(g[0] + px, g[1] + py)
    TB_COLS[i] = m
    SIG_COLS[i] = 1 << cidx(g[0] + 6, g[1])

ok_r2 = True
ok_tp = True
for v in KER_HXC:
    vL = v & ((1 << NC) - 1)
    vR = v >> NC
    z = apply_cols(TB_COLS, vL)
    bz = apply_cols(D2C_COV_COLS, z)
    sig_v = apply_cols(SIG_COLS, vL) | (apply_cols(SIG_COLS, vR) << NC)
    ok_r2 &= bz == (v ^ sig_v)
    # tau(p(v)) = (1 + sigma) v
    tpv = 0
    for blk in range(2):
        vv = ((v >> (blk * NC)) ^ (sig_v >> (blk * NC))) & ((1 << NC) - 1)
        # restrict to sheet 0 (x < 6) and lift to both sheets
        u = 0
        t = vv
        while t:
            b = t & -t
            i = b.bit_length() - 1
            x, y = i % CX, i // CX
            if x < 6:
                u |= 1 << bidx(x, y)
            t ^= b
        for sheet in range(2):
            t = u
            while t:
                b = t & -t
                i = b.bit_length() - 1
                tpv |= 1 << (blk * NC + cidx(i % BX + 6 * sheet, i // BX))
                t ^= b
    ok_tp &= tpv == (v ^ sig_v)
check("homotopy d2((1+x^2) B v_L) = v + sigma(v) on ALL 78 basis cycles "
      "of ker H_X^cov", ok_r2)
check("tau(p(v)) = (1 + sigma) v as a chain identity on the basis", ok_tp)

# orbits of ker d2 \ 0 under TRANSLATION ONLY; swap closure
orbsZ = {}
for z in zlist:
    key = min(translate36(z, dx, dy) for dx in range(6) for dy in range(6))
    orbsZ.setdefault(key, []).append(z)


def swap36_mask(z):
    out = 0
    while z:
        b = z & -z
        i = b.bit_length() - 1
        out |= 1 << bidx(i // BX, i % BX)     # (x,y) -> (y,x)
        z ^= b
    return out


sw_ok = True
for key, mem in orbsZ.items():
    sw = swap36_mask(key)
    skey = min(translate36(sw, dx, dy) for dx in range(6) for dy in range(6))
    sw_ok &= skey == key                       # swap stabilizes each orbit
sizes = sorted((len(v), popcount(k)) for k, v in orbsZ.items())
check("ker d2 \\ 0: 5 TRANSLATION orbits, (size, wt) = (3,24) x2, (9,16), "
      "(12,18), (36,18); swap preserves each",
      len(orbsZ) == 5 and sizes == [(3, 24), (3, 24), (9, 16), (12, 18),
                                    (36, 18)] and sw_ok)

ORB_KEYS = sorted(orbsZ, key=lambda k: (popcount(k), len(orbsZ[k])))
# disambiguate the two wt-24 orbits later by pin signature

# |d2c_j zeta| distribution and the per-orbit cut profiles
dist12 = Counter(popcount(apply_cols(D2S[0][1], z)) for z in zlist)
check("|d2c_0 zeta| over the 63: 18 reps of weight 12; values within "
      "{12,...,20}",
      dist12[12] == 18 and set(dist12) <= {12, 14, 16, 18, 20})
prof16 = sorted(popcount(apply_cols(D2S[j][1], ORB_KEYS[0]))
                for j in range(6))
prof24 = [Counter(popcount(apply_cols(D2S[j][1], k)) for j in range(6))
          for k in ORB_KEYS[3:]]
check("wt-16 orbit rep cut profile = {12 x4, 16 x2}; wt-24 reps sit at 20 "
      "for every cut",
      prof16 == [12, 12, 12, 12, 16, 16]
      and all(p == Counter({20: 6}) for p in prof24))

# flux: all 84 weight-6 logicals loud (every cut); hexagons silent
def flux(w, j):
    s = apply_cols(D1S[j][1], w)
    return tuple(popcount(x & s) & 1 for x in K0)


ok = all(any(flux(w, j)) for w in log6 for j in range(6))
ok &= all(not any(flux(w, 0)) for w in bnd6)
check("every weight-6 logical has NONZERO flux (all cuts); all 36 "
      "hexagons are flux-silent", ok)

# upper-bound witness tau(u*)
u_star = log6[0]
for w in log6:
    if (w >> N) == 0:                  # Ann(A)-type
        u_star = w
        break
tau_u = 0
for blk in range(2):
    vv = (u_star >> (blk * N)) & ((1 << N) - 1)
    while vv:
        b = vv & -vv
        i = b.bit_length() - 1
        x, y = i % BX, i // BX
        tau_u |= 1 << (blk * NC + cidx(x, y))
        tau_u |= 1 << (blk * NC + cidx(x + 6, y))
        vv ^= b
syn = 0
vv = tau_u
while vv:
    b = vv & -vv
    syn ^= HXC_COLS[b.bit_length() - 1]
    vv ^= b
check("upper-bound witness: tau(u*) has weight 12, is a cover cycle, and "
      "is NOT a cover boundary",
      popcount(tau_u) == 12 and syn == 0
      and SOLVE_D2COV.solve(tau_u) is None)


# =========================================================================
print("\n=== AV4: Entry 18 — no-double-wrap; flux characterization; pins ===")
ok_ndw = True
for j in range(6):
    d1nc, d1c = D1S[j]
    d2nc, d2c = D2S[j]
    for f in range(N):
        a = apply_cols(d1c, d2c[f])
        b = apply_cols(d1nc, d2nc[f])
        c1_ = apply_cols(d1nc, d2c[f])
        c2_ = apply_cols(d1c, d2nc[f])
        ok_ndw &= a == 0 and b == 0 and c1_ == c2_
check("d1c_j d2c_j = 0, d1nc_j d2nc_j = 0, d1nc d2c = d1c d2nc "
      "(matrix identities, all 6 cuts)", ok_ndw)

ok_wd = all(popcount(x & apply_cols(D1S[0][1], D2_COLS[f])) % 2 == 0
            for x in K0 for f in range(N))
check("flux functionals vanish on boundaries (well-defined on classes)",
      ok_wd)

# ker(flux) = im Delta as class sets
silent = set()
for hmask in range(4096):
    w = 0
    for i in range(12):
        if (hmask >> i) & 1:
            w ^= H1_BASIS[i]
    if not any(flux(w, 0)):
        silent.add(cls(w))
check("ker(flux) == im Delta as H1-class sets (64 = 64)",
      silent == set(imD_classes[0]))

# pins: offset of comp j realizable as (Bhat_j t, Ahat_j t)?
def comp_offsets(w):
    return {j: (comp_hat(w & ((1 << N) - 1), j), comp_hat(w >> N, j))
            for j in range(5)}


realizable = {j: {(rmul(BH[j], t), rmul(AH[j], t)) for t in ALL_F4T}
              for j in range(5)}
pin_sig = {}
for key in ORB_KEYS:
    offs = comp_offsets(apply_cols(D2S[0][1], key))
    pin_sig[key] = tuple(j for j in range(5)
                         if (offs[j][0], offs[j][1]) not in realizable[j])
# align the two wt-24 orbits by pin signature: 24a pinned {4}, 24b {3}
k24 = ORB_KEYS[3:]
if pin_sig[k24[0]] == (3,):
    ORB_KEYS[3], ORB_KEYS[4] = k24[1], k24[0]
pins = [pin_sig[k] for k in ORB_KEYS]
check("pins: wt-16 {3,4}; wt-18a {4}; wt-18b {3,4}; wt-24a {4}; wt-24b {3}",
      pins == [(3, 4), (4,), (3, 4), (4,), (3,)])
ONAMES = ["wt-16(n=9)", "wt-18a(n=12)", "wt-18b(n=36)", "wt-24a(n=3)",
          "wt-24b(n=3)"]


# =========================================================================
print("\n=== AV5: Entries 19/22 — transport, parity, rigidity, rho-locks, "
      "confined floors ===")
# class transport, exact: d2c_0(T zeta) + T d2c_0(zeta) in im d2,
# for all 63 zeta x 36 translations
ok_tr = True
for z in zlist:
    w = apply_cols(D2S[0][1], z)
    for dx in range(6):
        for dy in range(6):
            wt_ = apply_cols(D2S[0][1], translate36(z, dx, dy))
            ok_tr &= SOLVE_D2.solve(wt_ ^ translate72(w, dx, dy)) is not None
check("class transport class(T zeta) = T class(zeta), all 63 x 36, exact",
      ok_tr)
# the exact commutation behind it: d2c_j o T_x = T_x o d2c_{j-1} and
# d2c_j o T_y = T_y o d2c_j, as matrix identities
ok_cm = True
for j in range(6):
    for f in range(N):
        x, y = f % BX, f // BX
        fx = bidx(x + 1, y)
        ok_cm &= D2S[j][1][fx] == translate72(D2S[(j - 1) % 6][1][f], 1, 0)
        fy = bidx(x, y + 1)
        ok_cm &= D2S[j][1][fy] == translate72(D2S[j][1][f], 0, 1)
check("cut-shift commutation: d2c_j T_x = T_x d2c_(j-1), "
      "d2c_j T_y = T_y d2c_j (matrix identities, all cuts)", ok_cm)

# V2 column/row evenness + the column relation c_{i+3} = (y+y^2) c_i
ok_ev = True
for z in zlist:
    for i in range(6):
        colw = sum((z >> bidx(i, y)) & 1 for y in range(6))
        roww = sum((z >> bidx(x, i)) & 1 for x in range(6))
        ok_ev &= colw % 2 == 0 and roww % 2 == 0
        for y in range(6):
            lhs = (z >> bidx(i + 3, y)) & 1
            rhs = ((z >> bidx(i, y - 1)) & 1) ^ ((z >> bidx(i, y - 2)) & 1)
            ok_ev &= lhs == rhs
check("every column/row of every zeta is even; c_(i+3) = (y+y^2) c_i", ok_ev)

# V3 block parities + even coset weight
ok_p = True
for z in zlist:
    w = apply_cols(D2S[0][1], z)
    P4 = sum((z >> bidx(4, y)) & 1 for y in range(6))
    P345 = sum((z >> bidx(x, y)) & 1 for x in (3, 4, 5) for y in range(6))
    wl, wr = vec_weight_split(w)
    ok_p &= wl % 2 == P4 % 2 == 0 and wr % 2 == P345 % 2 == 0
ok_p &= all(popcount(D2_COLS[f]) % 2 == 0 for f in range(N))
check("|w0_L| == |P4 zeta|, |w0_R| == |(P3+P4+P5) zeta| == 0 (mod 2); "
      "|d2 t| even", ok_p)

# V4: value bijection + E <= 2 rigidity (own frame)
check("512 layers <-> 512 value tuples (bijection; no tuple missed)",
      int((WT >= 0).sum()) == 512)
pts = []
for tx in range(3):
    for ty in range(3):
        pts.append((1,) + tuple(WP[(c * tx + d * ty) % 3]
                                for j, (c, d) in R5.items() if j > 0))
e1 = {tuple(int(q) for q in p) for p in np.argwhere(WT == 1)}
e2 = {tuple(int(q) for q in p) for p in np.argwhere(WT == 2)}
prs = {tuple(a ^ b for a, b in zip(p, q))
       for p, q in combinations(pts, 2)}
ok_r = e1 == set(pts) and e2 == prs and len(e2) == 36 and \
    all(v[0] == 0 and sum(1 for j in range(1, 5) if v[j] == 0) == 1
        for v in e2)
check("E=1 cells = the 9 delta tuples; E=2 = the 36 pair sums "
      "(v0 = 0, exactly one dead comp)", ok_r)

# V5: rho-locks
rho1 = rmul(AH[1], rinv(BH[1]))
rho2 = rmul(BH[2], rinv(AH[2]))
imr1 = sorted({rmul(rho1, t) for t in ALL_F4T})
imr2 = sorted({rmul(rho2, t) for t in ALL_F4T})
ok_l = rmul(rho1, rho1) == (0, 0, 0, 0) and rmul(rho2, rho2) == (0, 0, 0, 0)
ok_l &= len(imr1) == 16 and len(imr2) == 16
ok_l &= set(imr1) == {rxor(smul(p, rho1), smul(q, XYr))
                      for p in range(4) for q in range(4)}
ok_l &= aug(rho1) == 0 and aug(rho2) == 0
check("rho_i^2 = 0; im rho_i = F4 rho_i + F4 XY (16 elements); aug 0",
      ok_l)
# unit/radical pattern + the comp-4 scalar tie (conjugate frame: w^2)
ok_c = AH[1] == AH[3] and BH[2] == BH[3] == BH[4]
ok_c &= aug(AH[1]) == 0 and aug(BH[2]) == 0 and aug(AH[4]) == 0
ok_c &= aug(BH[1]) == 1 and aug(AH[2]) == 1 and aug(AH[0]) == 1
scal = next((k for k in (2, 3) if smul(k, AH[4]) == BH[4]), None)
ok_c &= scal is not None
check(f"Ahat1 = Ahat3, Bhat2 = Bhat3 = Bhat4 (radical); Bhat1, Ahat2 "
      f"units; Bhat4 = scalar * Ahat4 (scalar = {scal}, i.e. w^2 in the "
      f"conjugate frame)", ok_c)

# Gamma parametrizations
G3 = {(rmul(BH[3], t), rmul(AH[3], t)) for t in ALL_F4T}
G3p = {(rxor(smul(a, BH[3]), smul(b, XYr)),
        rxor(smul(a, AH[3]), smul(c, XYr)))
       for a in range(4) for b in range(4) for c in range(4)}
G4 = {(rmul(BH[4], t), rmul(AH[4], t)) for t in ALL_F4T}
G4p = {(smul(scal, rxor(smul(a, AH[4]), smul(g, XYr))),
        rxor(smul(a, AH[4]), smul(g, XYr)))
       for a in range(4) for g in range(4)}
check("Gamma_3 = {(a Bhat3 + b XY, a Ahat3 + c XY)} (64, free shifts); "
      "Gamma_4 = {(w^k(a Ahat4 + g XY), a Ahat4 + g XY)} (16)",
      G3 == G3p and len(G3) == 64 and G4 == G4p and len(G4) == 16)

# c1 = c2 = 0 for ALL 63 zeta; off0 diagonal; SHARPER: off0 = off2 = 0
ok_c12 = ok_d0 = ok_z02 = True
for z in zlist:
    offs = comp_offsets(apply_cols(D2S[0][1], z))
    c1v = rxor(offs[1][1], rmul(rho1, offs[1][0]))
    c2v = rxor(offs[2][0], rmul(rho2, offs[2][1]))
    ok_c12 &= c1v == (0, 0, 0, 0) and c2v == (0, 0, 0, 0)
    ok_d0 &= offs[0][0] == offs[0][1]
    ok_z02 &= offs[0] == ((0,) * 4, (0,) * 4) and \
        offs[2] == ((0,) * 4, (0,) * 4)
check("c1 = c2 = 0 on all 63 zeta (comps 1, 2 unpinned)", ok_c12)
check("comp-0 offsets diagonal (Entry 19 parity lemma)", ok_d0)
check("SHARPENING (this review): off0 = off2 = 0 IDENTICALLY on all 63",
      ok_z02)

# V6 fibre gap (informational: not load-bearing, see Entry 27 log)
gaps = Counter()
nfib = 0
ok_g = True
for v0 in range(2):
    for v3 in range(4):
        for v4 in range(4):
            for a1 in range(2):
                for a2 in range(2):
                    d1 = (0,) if a1 == 0 else (1, 2, 3)
                    d2_ = (0,) if a2 == 0 else (1, 2, 3)
                    ws = sorted(int(WT[v0, q1, q2, v3, v4])
                                for q1 in d1 for q2 in d2_)
                    uq = sorted(set(ws))
                    if len(uq) > 1:
                        nfib += 1
                        gaps[uq[1] - uq[0]] += 1
                        ok_g &= all(x == uq[0] or x >= uq[0] + 4 for x in ws)
check("fibre gap: 66 nontrivial fibres, every non-minimal weight >= "
      "min + 4 (informational)", nfib == 66 and ok_g and set(gaps) == {4})

# confined floors (brute force, own frame)
ORB_OFFS = {k: comp_offsets(apply_cols(D2S[0][1], k)) for k in ORB_KEYS}


def cell_value(key, a3, a4):
    offs = ORB_OFFS[key]
    b3L = rxor(offs[3][0], smul(a3, BH[3]))
    b3R = rxor(offs[3][1], smul(a3, AH[3]))
    b4L = rxor(offs[4][0], smul(scal, smul(a4, AH[4])))
    b4R = rxor(offs[4][1], smul(a4, AH[4]))
    best = 10 ** 9
    for g in range(4):
        V4L = rxor(b4L, smul(F4M[scal][g], XYr))
        V4R = rxor(b4R, smul(g, XYr))
        for V0 in ALL_F2T:
            lmin = 10 ** 9
            for be in range(4):
                V3 = rxor(b3L, smul(be, XYr))
                for V2 in imr2:
                    tot = sum(int(M1[V0[s], V2[s], V3[s], V4L[s]])
                              for s in range(4))
                    lmin = min(lmin, tot)
            rmin = 10 ** 9
            for al in range(4):
                V3 = rxor(b3R, smul(al, XYr))
                for V1 in imr1:
                    tot = sum(int(M2[V0[s], V1[s], V3[s], V4R[s]])
                              for s in range(4))
                    rmin = min(rmin, tot)
            best = min(best, lmin + rmin)
    return best


CTAB = {}
for key in ORB_KEYS:
    CTAB[key] = {(a3, a4): cell_value(key, a3, a4)
                 for a3 in range(4) for a4 in range(4)}
floors = [min(CTAB[k].values()) for k in ORB_KEYS]
check("confined floors per orbit = 10/10/10/12/12",
      floors == [10, 10, 10, 12, 12])

# end-to-end: random ACTUAL coset elements decompose into the spine
# parametrization, satisfy both rho-links, and obey weight >= cell value
# (>= 12 in particular)
G3_dec = {}
for a in range(4):
    for b in range(4):
        for c in range(4):
            pair = (rxor(smul(a, BH[3]), smul(b, XYr)),
                    rxor(smul(a, AH[3]), smul(c, XYr)))
            G3_dec[pair] = a
G4_dec = {}
for a in range(4):
    for g in range(4):
        pr = rxor(smul(a, AH[4]), smul(g, XYr))
        G4_dec[(smul(scal, pr), pr)] = a
ok_e2e = True
for ki, key in enumerate(ORB_KEYS):
    w0 = apply_cols(D2S[0][1], key)
    offs = ORB_OFFS[key]
    for trial in range(200):
        t = 0
        for i in rng.choice(N, 7, replace=False):
            t ^= D2_COLS[int(i)]
        w = w0 ^ t
        co = comp_offsets(w)
        # spine decomposition
        p3 = (rxor(co[3][0], offs[3][0]), rxor(co[3][1], offs[3][1]))
        p4 = (rxor(co[4][0], offs[4][0]), rxor(co[4][1], offs[4][1]))
        if p3 not in G3_dec or p4 not in G4_dec:
            ok_e2e = False
            continue
        a3, a4 = G3_dec[p3], G4_dec[p4]
        # rho-links (c1 = c2 = 0)
        ok_e2e &= co[1][1] == rmul(rho1, co[1][0])
        ok_e2e &= co[2][0] == rmul(rho2, co[2][1])
        # weight >= linked cell value >= 10, and >= 12 (the endpoint)
        ww = popcount(w)
        ok_e2e &= ww >= CTAB[key][(a3, a4)] and ww >= 12
check("end-to-end: 200 random elements/orbit decompose into (spine, "
      "shifts, confined values), satisfy BOTH rho-links, and obey "
      "|w| >= m(cell) and |w| >= 12", ok_e2e)

# calibration of the whole engine on the ZERO class (im d2 itself):
# offsets 0 -> the linked floor must drop to 6 and a cost-6 config with
# BOTH links satisfiable must exist (the hexagons are real elements)
ZOFF = {j: ((0, 0, 0, 0), (0, 0, 0, 0)) for j in range(5)}


def zero_cell_value(a3, a4):
    b3L = smul(a3, BH[3])
    b3R = smul(a3, AH[3])
    b4L = smul(scal, smul(a4, AH[4]))
    b4R = smul(a4, AH[4])
    best = 10 ** 9
    for g in range(4):
        V4L = rxor(b4L, smul(F4M[scal][g], XYr))
        V4R = rxor(b4R, smul(g, XYr))
        for V0 in ALL_F2T:
            lmin = min(sum(int(M1[V0[s], V2[s],
                                  rxor(b3L, smul(be, XYr))[s], V4L[s]])
                           for s in range(4))
                       for be in range(4) for V2 in imr2)
            rmin = min(sum(int(M2[V0[s], V1[s],
                                  rxor(b3R, smul(al, XYr))[s], V4R[s]])
                           for s in range(4))
                       for al in range(4) for V1 in imr1)
            best = min(best, lmin + rmin)
    return best


zfloor = min(zero_cell_value(a3, a4) for a3 in range(4) for a4 in range(4))
zcell00 = zero_cell_value(0, 0)
# a hexagon (= d2 column) is a confined config (links satisfied) whose
# cell value is <= 6 = its weight
hexw = D2_COLS[0]
hco = {j: (comp_hat(hexw & ((1 << N) - 1), j), comp_hat(hexw >> N, j))
       for j in range(5)}
hex_links = (hco[1][1] == rmul(rho1, hco[1][0])
             and hco[2][0] == rmul(rho2, hco[2][1]))
p3h = hco[3]
p4h = hco[4]
hex_cell_ok = p3h in G3_dec and p4h in G4_dec and \
    zero_cell_value(G3_dec[p3h], G4_dec[p4h]) <= 6
# NOTE (1st-pass finding of this review): my initial calibration asserted
# zfloor == 6 and FAILED — correctly: the zero coset contains the zero
# element, so its linked floor is 0 (cell (0,0)).  The fixed calibration:
check("calibration on the zero class: floor = 0 (the zero element, cell "
      "(0,0)); the hexagon satisfies both rho-links and sits in a cell "
      "of value <= 6 (the machinery does NOT kill real elements)",
      zfloor == 0 and zcell00 == 0 and hex_links and hex_cell_ok
      and popcount(hexw) == 6)


# =========================================================================
print("\n=== AV6: Entries 23/24 — M-table hand rules; C-tables; wt-24 "
      "closure ===")
cen1 = Counter(int(M1[v0, a, b, c]) for v0 in range(2) for a in range(4)
               for b in range(4) for c in range(4))
check("M1 census {0:1, 1:9, 2:36, 3:55, 4:27}",
      dict(cen1) == {0: 1, 1: 9, 2: 36, 3: 55, 4: 27})
FROB = [0, 1, 3, 2]
check("M2(v0,a,b,c) == M1(v0,a,b,Frob c) (the swap symmetry)",
      all(M2[v0, a, b, c] == M1[v0, a, b, FROB[c]] for v0 in range(2)
          for a in range(4) for b in range(4) for c in range(4)))

# character identities in my (conjugate) frame
ok_ci = True
for tx in range(3):
    for ty in range(3):
        p1 = WP[(0 * tx + 2 * ty) % 3]
        p2 = WP[(2 * tx + 0 * ty) % 3]
        p3 = WP[(2 * tx + 2 * ty) % 3]
        p4 = WP[(2 * tx + 1 * ty) % 3]
        ok_ci &= F4M[p2][p2] == F4M[p3][p4] and F4M[p1][p3] == p4
check("character identities psi2^2 = psi3 psi4 and psi4 = psi1 psi3 "
      "(conjugate frame)", ok_ci)


def rule_M1(v0, v2, v3, v4):
    alive = sum(1 for v in (v2, v3, v4) if v)
    if v0 == 0:
        if alive == 0:
            return 0
        if alive == 1:
            return 4
        if alive == 2:
            return 2
        T = F4M[F4M[v2][v2]][F4INV[F4M[v3][v4]]]
        return 2 if T == 1 else 4
    if alive == 3:
        T = F4M[F4M[v2][v2]][F4INV[F4M[v3][v4]]]
        if T == 1:
            return 1
    return 3


def rule_M2(v0, v1, v3, v4):
    alive = sum(1 for v in (v1, v3, v4) if v)
    if v0 == 0:
        if alive == 0:
            return 0
        if alive == 1:
            return 4
        if alive == 2:
            return 2
        T = F4M[v4][F4INV[F4M[v1][v3]]]
        return 2 if T == 1 else 4
    if alive == 3:
        T = F4M[v4][F4INV[F4M[v1][v3]]]
        if T == 1:
            return 1
    return 3


ok_rule = all(rule_M1(v0, a, b, c) == int(M1[v0, a, b, c])
              and rule_M2(v0, a, b, c) == int(M2[v0, a, b, c])
              for v0 in range(2) for a in range(4) for b in range(4)
              for c in range(4))
check("the HAND RULES (alive count + T-classifier) reproduce M1 AND M2 "
      "on all 128 cells each", ok_rule)

# 18 orbits of M1 cells under 9 translations x Frobenius
scals = []
for r1 in range(3):
    for r2 in range(3):
        scals.append((WP[(2 * r1) % 3], WP[(2 * r1 + 2 * r2) % 3],
                      WP[(2 * r1 + r2) % 3]))
ocells = {}
for v0 in range(2):
    for a in range(4):
        for b in range(4):
            for c in range(4):
                reps = []
                for (s2, s3, s4) in scals:
                    t = (v0, F4M[s2][a], F4M[s3][b], F4M[s4][c])
                    reps.append(t)
                    reps.append((v0, FROB[t[1]], FROB[t[2]], FROB[t[3]]))
                ocells.setdefault(min(reps), 0)
                ocells[min(reps)] += 1
check("M1 cells fall in 18 orbits under (9 translations) x Frobenius",
      len(ocells) == 18)

# spine C-tables: multisets, floor-10 cell counts, wt-24 block minima
msets = [sorted(Counter(CTAB[k].values()).items()) for k in ORB_KEYS]
check("C-table value multisets: wt-16 {10:4, 12:12}; wt-18a {10:14, 12:2}; "
      "wt-18b {10:12, 12:4}",
      msets[0] == [(10, 4), (12, 12)] and msets[1] == [(10, 14), (12, 2)]
      and msets[2] == [(10, 12), (12, 4)])
check("wt-24 C-tables: all 16 cells >= 12 on both wt-24 orbits",
      all(v >= 12 for k in ORB_KEYS[3:] for v in CTAB[k].values()))


def block_min(key, a3, a4, blk):
    offs = ORB_OFFS[key]
    if blk == 0:
        b3 = rxor(offs[3][0], smul(a3, BH[3]))
        b4 = rxor(offs[4][0], smul(scal, smul(a4, AH[4])))
        Mt, conf = M1, imr2
    else:
        b3 = rxor(offs[3][1], smul(a3, AH[3]))
        b4 = rxor(offs[4][1], smul(a4, AH[4]))
        Mt, conf = M2, imr1
    best = 10 ** 9
    for V0 in ALL_F2T:
        for g in range(4):
            V4 = rxor(b4, smul(g, XYr))
            for sh in range(4):
                V3 = rxor(b3, smul(sh, XYr))
                for Vc in conf:
                    tot = sum(int(Mt[V0[s], Vc[s], V3[s], V4[s]])
                              for s in range(4))
                    best = min(best, tot)
    return best


ok_b6 = all(block_min(key, a3, a4, blk) == 6
            for key in ORB_KEYS[3:] for a3 in range(4) for a4 in range(4)
            for blk in (0, 1))
check("wt-24 orbits: EVERY unlinked block minimum equals 6 (2 orbits x "
      "16 cells x 2 blocks) -> every cell >= 12", ok_b6)

stabs = []
for key in ORB_KEYS:
    stabs.append(sum(1 for dx in range(6) for dy in range(6)
                     if translate36(key, dx, dy) == key))
check("translation stabilizer orders (wt-16, 18a, 18b, 24a, 24b) = "
      "(4, 3, 1, 12, 12)", stabs == [4, 3, 1, 12, 12])


# =========================================================================
print("\n=== AV7: Entry 25 — achiever enumeration + rho-link kills ===")
KERr1 = [t for t in ALL_F4T if rmul(rho1, t) == (0, 0, 0, 0)]
KERr2 = [t for t in ALL_F4T if rmul(rho2, t) == (0, 0, 0, 0)]
check("|ker rho1| = |ker rho2| = 16", len(KERr1) == 16 and len(KERr2) == 16)

grand_ok = True
ach_counts = []
kill_stats = []
for key in ORB_KEYS[:3]:
    offs = ORB_OFFS[key]
    total = killed = one_link = 0
    cell_hist = Counter()
    for a3 in range(4):
        for a4 in range(4):
            b3L = rxor(offs[3][0], smul(a3, BH[3]))
            b3R = rxor(offs[3][1], smul(a3, AH[3]))
            b4L = rxor(offs[4][0], smul(scal, smul(a4, AH[4])))
            b4R = rxor(offs[4][1], smul(a4, AH[4]))
            for g in range(4):
                V4L = rxor(b4L, smul(F4M[scal][g], XYr))
                V4R = rxor(b4R, smul(g, XYr))
                for V0 in ALL_F2T:
                    Ls = []
                    for be in range(4):
                        V3 = rxor(b3L, smul(be, XYr))
                        for V2 in imr2:
                            c = sum(int(M1[V0[s], V2[s], V3[s], V4L[s]])
                                    for s in range(4))
                            if c <= 10:
                                Ls.append((c, V3, V2))
                    Rs = []
                    for al in range(4):
                        V3 = rxor(b3R, smul(al, XYr))
                        for V1 in imr1:
                            c = sum(int(M2[V0[s], V1[s], V3[s], V4R[s]])
                                    for s in range(4))
                            if c <= 10:
                                Rs.append((c, V3, V1))
                    for cL, V3L, V2L in Ls:
                        for cR, V3R, V1R in Rs:
                            if cL + cR != 10:
                                continue
                            total += 1
                            cell_hist[(a3, a4)] += 1
                            min1 = []
                            for s in range(4):
                                mv = int(M1[V0[s], V2L[s], V3L[s], V4L[s]])
                                min1.append([v for v in range(4)
                                             if int(WT[V0[s], v, V2L[s],
                                                       V3L[s], V4L[s]]) == mv])
                            min2 = []
                            for s in range(4):
                                mv = int(M2[V0[s], V1R[s], V3R[s], V4R[s]])
                                min2.append([v for v in range(4)
                                             if int(WT[V0[s], V1R[s], v,
                                                       V3R[s], V4R[s]]) == mv])
                            t0 = next(t for t in ALL_F4T
                                      if rmul(rho1, t) == V1R)
                            ok1 = any(all(rxor(t0, kk)[s] in min1[s]
                                          for s in range(4)) for kk in KERr1)
                            u0 = next(t for t in ALL_F4T
                                      if rmul(rho2, t) == V2L)
                            ok2 = any(all(rxor(u0, kk)[s] in min2[s]
                                          for s in range(4)) for kk in KERr2)
                            if not (ok1 and ok2):
                                killed += 1
                                if ok1 or ok2:
                                    one_link += 1
    ach_counts.append(total)
    kill_stats.append((killed, one_link, len(cell_hist),
                       sorted(cell_hist.values())))
    grand_ok &= killed == total
check("achiever counts (wt-16, 18a, 18b) = (48, 48, 22)",
      ach_counts == [48, 48, 22])
check("wt-16: 12 achievers at each of 4 cells; wt-18a spread over 14 "
      "cells; wt-18b over 12",
      kill_stats[0][2:] == (4, [12, 12, 12, 12])
      and kill_stats[1][2] == 14 and kill_stats[2][2] == 12)
check("EVERY achiever violates a dropped rho-link (no weight-10 coset "
      "elements)", grand_ok)
check("exception structure: exactly 2 achievers (wt-18b) fail exactly "
      "one link; all others fail both",
      [k[1] for k in kill_stats] == [0, 0, 2])


# =========================================================================
print("\n=== AV8: Entry 21 — own weight-8/10 census; the (M-im) endpoint "
      "independently ===")
KA = np.array(span(ANN_A), dtype=np.int64)       # 4096 Ann(A) elements
KB = np.array(span(ANN_B), dtype=np.int64)
SOLVE_MA = F2Solver(MA_COLS)
SOLVE_MB = F2Solver(MB_COLS)


def census_high(Wt):
    """All 1-cycles of weight Wt as (mL, mR), by split, own method."""
    out = {}
    # pure splits
    pure = [(popcount(int(z)), int(z)) for z in KA]
    fa = [(z, 0) for w_, z in pure if w_ == Wt]
    fb = [(0, int(z)) for z in KB if popcount(int(z)) == Wt]
    if fa:
        out[(Wt, 0)] = fa
    if fb:
        out[(0, Wt)] = fb
    # mixed: small side k on one block, kernel-coset scan on the other
    for k in range(1, Wt // 2 + 1):
        kk = Wt - k
        if k == kk:
            break
        # split (kk, k): right side small
        found = []
        for T in combinations(range(N), k):
            s = 0
            mR = 0
            for i in T:
                s ^= MB_COLS[i]
                mR |= 1 << i
            xp = SOLVE_MA.solve(s)
            if xp is None:
                continue
            ws = np.bitwise_count(KA ^ np.int64(xp))
            for idx in np.flatnonzero(ws == kk):
                found.append((int(KA[idx]) ^ xp, mR))
        if found:
            out[(kk, k)] = found
        # split (k, kk): left side small
        found = []
        for T in combinations(range(N), k):
            s = 0
            mL = 0
            for i in T:
                s ^= MA_COLS[i]
                mL |= 1 << i
            xp = SOLVE_MB.solve(s)
            if xp is None:
                continue
            ws = np.bitwise_count(KB ^ np.int64(xp))
            for idx in np.flatnonzero(ws == kk):
                found.append((mL, int(KB[idx]) ^ xp))
        if found:
            out[(k, kk)] = found
    # balanced split by syndrome hash-join
    h = Wt // 2
    left = {}
    for T in combinations(range(N), h):
        s = 0
        mL = 0
        for i in T:
            s ^= MA_COLS[i]
            mL |= 1 << i
        left.setdefault(s, []).append(mL)
    found = []
    for T in combinations(range(N), h):
        s = 0
        mR = 0
        for i in T:
            s ^= MB_COLS[i]
            mR |= 1 << i
        for mL in left.get(s, ()):
            found.append((mL, mR))
    if found:
        out[(h, h)] = found
    return out


c8 = census_high(8)
n8 = sum(len(v) for v in c8.values())
spl8 = {k: len(v) for k, v in c8.items()}
check("weight-8 census: 990 cycles; splits (8,0):9 (5,3):108 (4,4):756 "
      "(3,5):108 (0,8):9",
      n8 == 990 and spl8 == {(8, 0): 9, (5, 3): 108, (4, 4): 756,
                             (3, 5): 108, (0, 8): 9})
all8 = [mL | (mR << N) for v in c8.values() for (mL, mR) in v]
bnd8 = sum(1 for w in all8 if SOLVE_D2.solve(w) is not None)
loud8 = sum(1 for w in all8 if any(flux(w, 0)))
check("weight-8: zero boundaries; ALL 990 flux-loud", bnd8 == 0
      and loud8 == 990)
orb8 = {min(translate72(w, dx, dy) for dx in range(6) for dy in range(6))
        for w in all8}
check("weight-8: 32 translation orbits", len(orb8) == 32)

c10 = census_high(10)
n10 = sum(len(v) for v in c10.values())
spl10 = {k: len(v) for k, v in c10.items()}
check("weight-10 census: 13464 cycles; splits (7,3):972 (6,4):3276 "
      "(5,5):4968 + mirrors; (9,1)/(8,2)/(10,0) EMPTY",
      n10 == 13464 and spl10 == {(7, 3): 972, (6, 4): 3276, (5, 5): 4968,
                                 (4, 6): 3276, (3, 7): 972})
all10 = [mL | (mR << N) for v in c10.values() for (mL, mR) in v]
bnd10 = [w for w in all10 if SOLVE_D2.solve(w) is not None]
nonb10 = [w for w in all10 if SOLVE_D2.solve(w) is None]
check("weight-10: exactly 216 boundaries (the D-pairs)", len(bnd10) == 216)
silent10 = sum(1 for w in nonb10 if not any(flux(w, 0)))
check("weight-10: ZERO flux-silent non-boundaries (all 13248 loud)",
      silent10 == 0 and len(nonb10) == 13248)
orb10 = {min(translate72(w, dx, dy) for dx in range(6) for dy in range(6))
         for w in nonb10}
check("weight-10 non-boundaries: 368 translation orbits", len(orb10) == 368)
print("  => independent re-verification of the (M-im) endpoint: no cycle "
      "of weight 6/8/10\n     lies in a nonzero im Delta class (silent "
      "non-boundaries do not exist below 12).")


# =========================================================================
print("\n=== AV9: Entry 26 — the unpinnedness chains in transform "
      "coordinates ===")
# my comp-1 rep is (0,2): u_i = sum_y c_i(y) w^{2(y%3)} s_y^{y%2};
# tau' = w + w^2 s_y; D1': Y u1 = w Y u2;
# reduced identity: Y[(X + w^2) u1 + (1 + w X) u2] = 0.


def ymul(a, b):
    return (F4M[a[0]][b[0]] ^ F4M[a[1]][b[1]],
            F4M[a[0]][b[1]] ^ F4M[a[1]][b[0]])


def yxor(a, b):
    return (a[0] ^ b[0], a[1] ^ b[1])


def u_tr(z, i):
    out = (0, 0)
    for y in range(6):
        if (z >> bidx(i, y)) & 1:
            t = WP[(2 * (y % 3)) % 3]
            out = yxor(out, (t, 0) if y % 2 == 0 else (0, t))
    return out


def v_tr(z, i):
    out = (0, 0)
    for y in range(6):
        if (z >> bidx(i, y)) & 1:
            out = yxor(out, (1, 0) if y % 2 == 0 else (0, 1))
    return out


def emb(u, sx_pow):
    # slot encoding: s = 2*(x%2) + (y%2)
    if sx_pow == 0:
        return (u[0], u[1], 0, 0)
    return (0, 0, u[0], u[1])


TAUc = (2, 3)                                   # w + w^2 s_y (conjugate)
SYt = (0, 1)
Yt = (1, 1)
ok_u1 = ok_ar = ok_b = ok_d1 = ok_red = ok_end1 = True
ok_v0 = ok_end2 = True
for z in zlist:
    w = apply_cols(D2S[0][1], z)
    off1 = (comp_hat(w & ((1 << N) - 1), 1), comp_hat(w >> N, 1))
    u = [u_tr(z, i) for i in range(6)]
    lhsL = rxor(rxor(emb(u[4], 0), emb(u[5], 0)), emb(u[5], 1))
    lhsR = rxor(rxor(emb(u[3], 0), emb(u[4], 1)), emb(u[5], 0))
    ok_u1 &= lhsL == off1[0] and lhsR == off1[1]
    for i in range(3):
        ok_ar &= u[i + 3] == ymul(TAUc, u[i])
    ok_b &= yxor(u[0], u[1]) == ymul(SYt, u[2])          # R2
    ok_b &= yxor(u[0], ymul(TAUc, u[2])) == ymul(SYt, u[1])   # R1
    ok_d1 &= ymul(Yt, u[1]) == ymul(Yt, ymul((2, 0), u[2]))   # Y u1 = w Y u2
    # reduced identity Y[(X + w^2) u1 + (1 + w X) u2] = 0
    Xw2 = rxor(emb((3, 0), 0), (0, 0, 1, 0))    # w^2 + s_x ... X + w^2
    # X + w^2 = (1 + s_x) + w^2 = (1 + w^2) + s_x = w + s_x
    Xw2 = (2, 0, 1, 0)
    onewX = (3, 0, 2, 0)                        # 1 + w X = (1+w) + w s_x
    Yfull = (1, 1, 0, 0)                        # Y = 1 + s_y in my slots
    expr = rmul(Yfull, rxor(rmul(Xw2, emb(u[1], 0)),
                            rmul(onewX, emb(u[2], 0))))
    ok_red &= expr == (0, 0, 0, 0)
    ok_end1 &= rmul(BH[1], off1[1]) == rmul(AH[1], off1[0])
    # comp 2: the collapse v_i = 0 (=> off2 = 0 outright)
    v = [v_tr(z, i) for i in range(6)]
    ok_v0 &= all(vi == (0, 0) for vi in v)
    off2 = (comp_hat(w & ((1 << N) - 1), 2), comp_hat(w >> N, 2))
    ok_end2 &= off2 == ((0, 0, 0, 0), (0, 0, 0, 0))
check("U1 crossing bookkeeping: off1L = u4+u5+s_x u5, "
      "off1R = u3+s_x u4+u5 (all 63)", ok_u1)
check("A-relation u_(i+3) = tau' u_i (tau' = w + w^2 s_y, conjugate "
      "frame)", ok_ar)
check("B-relations R1, R2", ok_b)
check("D1 (conjugate frame): Y u1 = w Y u2", ok_d1)
check("reduced identity Y[(X + w^2) u1 + (1 + w X) u2] = 0", ok_red)
check("endpoint comp 1: Bhat1 off1R = Ahat1 off1L (c1 = 0)", ok_end1)
check("comp-2 collapse (this review): v_i = 0 for ALL columns of ALL "
      "zeta (Y^2 = 0 argument) => off2 = 0 => c2 = 0 in one line",
      ok_v0 and ok_end2)


# =========================================================================
print("\n" + "=" * 73)
fails = [n for n, ok in RESULTS if not ok]
print(f"TOTAL: {len(RESULTS)} checks, {len(RESULTS) - len(fails)} passed, "
      f"{len(fails)} failed.")
if fails:
    print("FAILED:")
    for n in fails:
        print(f"  - {n}")
else:
    print("ALL CHECKS PASS — the counterexample hunt over Entries 16-26 "
          "failed.")

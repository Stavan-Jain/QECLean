"""A3 / Track 1.1 Entry 15 — adversarial re-review of the d(gross) >= 6 chain.

INDEPENDENT re-implementation of every load-bearing machine check behind
Entries 5 and 10-14.  Deliberately uses a different encoding path from the
lab's scripts (`bb_lab.checks` / `bb_lab.linalg` are NOT imported):

  - own group indexing (y-major idx(x,y) = y*XN + x, vs the lab's x-major
    row-major) — catches transposition/convention bugs;
  - own F2 linear algebra on Python int bitmasks (rref / nullspace / solve),
    vs the lab's numpy Gaussian elimination;
  - own group-algebra products via cell-set symmetric differences;
  - membership in im(A.) via direct solve, vs the lab's dual-nullspace dots;
  - the light-stabilizer classification re-checked by SAT (pysat, generator-
    side encoding b = d2.z + cardinality), vs the lab's layer-profile
    hash-join — SAT used strictly as a counterexample HUNTER;
  - own CRT frame (layers = mod-2 parities, cells = mod-3 parts, own F4
    tables and characters), with the transform multiplicativity itself
    re-verified on the delta basis rather than assumed.

Sections (each prints PASS/FAIL; summary at the end):

  AV1  difference sets; FULL overlap table (ov = 1 iff delta in D, else 0);
       hexagon weight 6; D-pair weight 10.
  AV2  Entry-13 small-cycle theorem: exhaustive meet-in-middle over all
       weight splits a+b <= 5 (both ker H_X and ker H_Z): zero nonzero
       cycles; weight-6 census = 120; the W4/W5 hand-proof intermediates
       (triangle classes/images, Ann(1+x+x^2), x-multiplicity multisets).
  AV3  light-stabilizer classification by SAT: |b| in {1..5,7,8,9,11} UNSAT;
       |b| = 6 -> exactly the 36 hexagons; |b| = 10 -> exactly the 216
       D-pairs.  (Independent of BOTH the lab's hash-join AND its SATs.)
  AV4  Entry-5 foundations, exact (no sampling): per-cut block form for H_X
       and H_Z, all 6 cuts; seam containment supp(d2c_j delta_g) in h(g);
       dangerous space = tau(Z1) + im(d2cov) (exact rref equality, dim 72);
       U0 := {u in Z1 : tau(u) in im d2cov} = im(Delta_j) + Stab for EVERY
       cut (Smith exactness + the nontriviality bridge, exact, basis-level).
  AV5  inversion duality Phi, re-derived: Phi(ker H_X) = ker H_Z and
       Phi(rowspace H_Z) = rowspace H_X, base AND cover, exact on bases.
  AV6  CRT-frame shape-lemma intermediates, own frame: d3 dictionary (512
       brute force); transform multiplicativity; unit/radical pattern;
       Ann(Ahat_j) = (Ahat_j) per radical component (256-element ring
       enumeration); Ann(A) min weight 6 / all even (4096); one-block exact
       min 16 both sides; the shape enumerations ((1,1,1) = 36 A.deltas,
       (2,1,1) = 108 A.(dA-pairs), (3,1,1) = 0 both sides, (2,1,1,1) = 36
       with completion min 9, (2,2,1) = 108 single-fibre with completion
       min 9, (1,1,1,1) = 9 delta-columns with completion min 12); the
       D-pair endgame (light completions = exactly the 64 kernel elements,
       non-kernel min >= 12, all 3 classes); the kappa_4 = kappa_1*kappa_3
       violation for every dead-orbit-2 triangle; t_y direction forcing;
       the parity lemma on the delta basis.

Computation may REFUTE but never PROVE: everything here is a hunt for a
counterexample to an intermediate claim of the hand proofs.  All-PASS means
the hunt failed, not that the proofs are machine-verified.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations, product

RESULTS: list[tuple[str, bool]] = []


def check(name: str, ok: bool):
    RESULTS.append((name, bool(ok)))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")


# =========================================================================
# F2 linear algebra on int bitmasks (own implementation)
# =========================================================================
def rref(vecs):
    """Self-reduced basis of span(vecs) as list of (pivot, vec)."""
    basis = []
    for v in vecs:
        for p, bv in basis:
            if (v >> p) & 1:
                v ^= bv
        if v:
            p = v.bit_length() - 1
            basis = [(q, bv ^ v if (bv >> p) & 1 else bv) for q, bv in basis]
            basis.append((p, v))
    return basis


def in_span(basis, v):
    for p, bv in basis:
        if (v >> p) & 1:
            v ^= bv
    return v == 0


def span_equal(b1, b2):
    return (len(b1) == len(b2) and all(in_span(b1, v) for _, v in b2)
            and all(in_span(b2, v) for _, v in b1))


def nullspace(cols):
    """cols: list of m-bit ints (columns of M). Basis of {x : M x = 0}."""
    basis, null = [], []
    for i, s in enumerate(cols):
        c = 1 << i
        for p, bs, bc in basis:
            if (s >> p) & 1:
                s ^= bs
                c ^= bc
        if s == 0:
            null.append(c)
        else:
            basis.append((s.bit_length() - 1, s, c))
    return null


def make_solver(cols):
    """Return solve(b) -> x with M x = b (or None), M given by columns."""
    basis = []
    for i, s in enumerate(cols):
        c = 1 << i
        for p, bs, bc in basis:
            if (s >> p) & 1:
                s ^= bs
                c ^= bc
        if s:
            basis.append((s.bit_length() - 1, s, c))

    def solve(b):
        x = 0
        for p, bs, bc in basis:
            if (b >> p) & 1:
                b ^= bs
                x ^= bc
        return x if b == 0 else None

    return solve


def apply_cols(cols, x):
    out = 0
    while x:
        out ^= cols[(x & -x).bit_length() - 1]
        x &= x - 1
    return out


def span_iter(gens):
    out = [0]
    for g in gens:
        out += [v ^ g for v in out]
    return out


def transpose_cols(rows, ncols):
    """rows: list of ncols-bit ints. Return list of len(rows)-bit columns."""
    return [sum(((rows[r] >> i) & 1) << r for r in range(len(rows)))
            for i in range(ncols)]


# =========================================================================
# Code construction from scratch (y-major indexing)
# =========================================================================
SUPP_A = [(3, 0), (0, 1), (0, 2)]      # x^3 + y + y^2
SUPP_B = [(0, 3), (1, 0), (2, 0)]      # y^3 + x + x^2


class BB:
    def __init__(self, xn, yn):
        self.xn, self.yn = xn, yn
        self.n = xn * yn
        self.elems = [(x, y) for y in range(yn) for x in range(xn)]  # y-major

    def idx(self, g):
        return (g[1] % self.yn) * self.xn + (g[0] % self.xn)

    def mul_set(self, supp, cells):
        out = set()
        for s in supp:
            for c in cells:
                out ^= {((s[0] + c[0]) % self.xn, (s[1] + c[1]) % self.yn)}
        return out

    def vec(self, cells):
        v = 0
        for c in cells:
            v ^= 1 << self.idx(c)
        return v

    # qubit vector: left block bits [0, n), right block [n, 2n)
    def hx_rows(self):
        """X-check g: M_A[g,h] = A(g-h) left, M_B right."""
        rows = []
        for g in self.elems:
            r = 0
            for s in SUPP_A:
                r |= 1 << self.idx((g[0] - s[0], g[1] - s[1]))
            for s in SUPP_B:
                r |= 1 << (self.n + self.idx((g[0] - s[0], g[1] - s[1])))
            rows.append(r)
        return rows

    def hz_rows(self):
        """Z-check g: [M_B^T | M_A^T]: left entry at h iff B(h-g)."""
        rows = []
        for g in self.elems:
            r = 0
            for s in SUPP_B:
                r |= 1 << self.idx((g[0] + s[0], g[1] + s[1]))
            for s in SUPP_A:
                r |= 1 << (self.n + self.idx((g[0] + s[0], g[1] + s[1])))
            rows.append(r)
        return rows


base = BB(6, 6)
cover = BB(12, 6)
HXb, HZb = base.hx_rows(), base.hz_rows()
HXc, HZc = cover.hx_rows(), cover.hz_rows()
D2b = HZb[:]                            # Z-stabilizer columns (face g -> qubits)
D2c = HZc[:]

print("=== AV0: own construction sanity ===")
check("CSS commutation H_X . H_Z^T = 0 (base and cover)",
      all((HXb[i] & D2b[j]).bit_count() % 2 == 0 for i in range(36) for j in range(36))
      and all((HXc[i] & D2c[j]).bit_count() % 2 == 0
              for i in range(72) for j in range(72)))

# =========================================================================
print("\n=== AV1: difference sets, overlap table, hexagons, D-pairs ===")
# =========================================================================
def diffset(supp):
    return {((a[0] - b[0]) % 6, (a[1] - b[1]) % 6)
            for a in supp for b in supp if a != b}


dA, dB = diffset(SUPP_A), diffset(SUPP_B)
check("dA = {(0,±1),(3,±1),(3,±2)}",
      dA == {(0, 1), (0, 5), (3, 1), (3, 5), (3, 2), (3, 4)})
check("dB = swap(dA); dA cap dB = empty",
      dB == {(d[1], d[0]) for d in dA} and not (dA & dB))

hexes = {g: D2b[base.idx(g)] for g in base.elems}
check("all 36 hexagons have weight 6", all(h.bit_count() == 6 for h in hexes.values()))

D = dA | dB
ov_ok = True
for g in base.elems:
    for d in [(x, y) for x in range(6) for y in range(6) if (x, y) != (0, 0)]:
        g2 = ((g[0] + d[0]) % 6, (g[1] + d[1]) % 6)
        ov = (hexes[g] & hexes[g2]).bit_count()
        ov_ok &= (ov == 1) if d in D else (ov == 0)
check("FULL overlap table: |h(g) cap h(g+d)| = 1 iff d in D else 0 (36 x 35)", ov_ok)
check("all 216 D-pairs have weight 10",
      {(hexes[g] ^ hexes[((g[0] + d[0]) % 6, (g[1] + d[1]) % 6)]).bit_count()
       for g in base.elems for d in D} == {10})

# =========================================================================
print("\n=== AV2: small-cycle theorem, exhaustive (independent path) ===")
# =========================================================================
colA = [base.vec(base.mul_set(SUPP_A, [g])) for g in base.elems]
colB = [base.vec(base.mul_set(SUPP_B, [g])) for g in base.elems]
iSUPP_A = [((-s[0]) % 6, (-s[1]) % 6) for s in SUPP_A]
iSUPP_B = [((-s[0]) % 6, (-s[1]) % 6) for s in SUPP_B]
colBT = [base.vec(base.mul_set(iSUPP_B, [g])) for g in base.elems]
colAT = [base.vec(base.mul_set(iSUPP_A, [g])) for g in base.elems]


def syndromes_upto(cols, kmax):
    out = {k: Counter() for k in range(1, kmax + 1)}

    def rec(start, depth, acc):
        if depth:
            out[depth][acc] += 1
        if depth == kmax:
            return
        for i in range(start, len(cols)):
            rec(i + 1, depth + 1, acc ^ cols[i])

    rec(0, 0, 0)
    return out


def count_small_cycles(SL, SR, wmax):
    bad = 0
    for a in range(0, wmax + 1):
        for b in range(0, wmax + 1 - a):
            if a + b == 0:
                continue
            if a == 0:
                bad += SR[b].get(0, 0)
            elif b == 0:
                bad += SL[a].get(0, 0)
            else:
                bad += sum(c * SR[b].get(k, 0) for k, c in SL[a].items())
    return bad


SLX = syndromes_upto(colA, 6)
SRX = syndromes_upto(colB, 6)
check("ker H_X: zero nonzero cycles of weight <= 5",
      count_small_cycles(SLX, SRX, 5) == 0)
SLZ = syndromes_upto(colBT, 5)
SRZ = syndromes_upto(colAT, 5)
check("ker H_Z: zero nonzero cycles of weight <= 5",
      count_small_cycles(SLZ, SRZ, 5) == 0)

census = SLX[6].get(0, 0) + SRX[6].get(0, 0)
for a in range(1, 6):
    census += sum(c * SRX[6 - a].get(k, 0) for k, c in SLX[a].items())
check("weight-6 cycle census in ker H_X = 120", census == 120)


def triangles(Dset):
    tris = set()
    for a in Dset:
        for b in Dset:
            if a != b and ((b[0] - a[0]) % 6, (b[1] - a[1]) % 6) in Dset:
                cells = [(0, 0), a, b]
                canon = min(tuple(sorted(((c[0] - t[0]) % 6, (c[1] - t[1]) % 6)
                                         for c in cells)) for t in cells)
                tris.add(canon)
    return sorted(tris)


triB = triangles(dB)
imgsB = [base.mul_set(SUPP_B, t) for t in triB]
okW4 = (len(triB) == 2 and sorted(len(i) for i in imgsB) == [3, 7]
        and all(len({c[1] for c in img}) == 1 for img in imgsB if len(img) == 3))
check("dB-triangles: 2 classes; image weights {3,7}; the 3-image is constant-y", okW4)
triA = triangles(dA)
imgsA = [base.mul_set(SUPP_A, t) for t in triA]
check("dA-triangles: mirror (constant-x 3-image)",
      len(triA) == 2 and sorted(len(i) for i in imgsA) == [3, 7]
      and all(len({c[0] for c in img}) == 1 for img in imgsA if len(img) == 3))
check("A.delta_g has 3 distinct y-coords (all g); B mirror in x",
      all(len({c[1] for c in base.mul_set(SUPP_A, [g])}) == 3 for g in base.elems)
      and all(len({c[0] for c in base.mul_set(SUPP_B, [g])}) == 3 for g in base.elems))


def xmultiset(cells):
    return tuple(sorted(Counter(c[0] for c in cells).values()))


check("sigma_A = A(1+x^3y): x-multiset (1,3); sigma_B = B(1+xy^3): (1,1,2); differ",
      xmultiset(base.mul_set(SUPP_A, [(0, 0), (3, 1)])) == (1, 3)
      and xmultiset(base.mul_set(SUPP_B, [(0, 0), (1, 3)])) == (1, 1, 2))

annw = []
for mask in range(1, 64):
    conv = set()
    for i in range(6):
        if (mask >> i) & 1:
            for s in (0, 1, 2):
                conv ^= {(i + s) % 6}
    if not conv:
        annw.append(bin(mask).count("1"))
check("Ann(1+x+x^2) in F2[Z6]: min weight 4", min(annw) == 4)

# =========================================================================
print("\n=== AV3: light-stabilizer classification via SAT (refutation hunt) ===")
# =========================================================================
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

face_of_qubit = [[j for j in range(36) if (D2b[j] >> i) & 1] for i in range(72)]
check("each qubit row of d2 has exactly 3 faces",
      all(len(f) == 3 for f in face_of_qubit))


def sat_weight_models(w, enumerate_models=False):
    pool = IDPool(start_from=200)
    bvars = list(range(1, 73))
    zvars = list(range(73, 109))
    cnf = []
    for i in range(72):
        a, b, c = (zvars[j] for j in face_of_qubit[i])
        o = bvars[i]
        cnf += [[-o, a, b, c], [-o, a, -b, -c], [-o, -a, b, -c], [-o, -a, -b, c],
                [o, -a, b, c], [o, a, -b, c], [o, a, b, -c], [o, -a, -b, -c]]
    cnf += CardEnc.equals(lits=bvars, bound=w, vpool=pool,
                          encoding=EncType.seqcounter).clauses
    models = []
    with Solver(name="g3", bootstrap_with=cnf) as s:
        while s.solve():
            m = s.get_model()
            bset = frozenset(i for i in range(72) if m[bvars[i] - 1] > 0)
            if not enumerate_models:
                return [bset]
            models.append(bset)
            s.add_clause([-bvars[i] if i in bset else bvars[i] for i in range(72)])
    return models


empty_ok = True
for w in [1, 2, 3, 4, 5, 7, 8, 9, 11]:
    ms = sat_weight_models(w)
    if ms:
        empty_ok = False
        print(f"    !! weight-{w} stabilizer found: {sorted(ms[0])}")
check("no stabilizers of weight 1-5, 7-9, 11 (9 UNSAT calls)", empty_ok)

hex_set = {frozenset(i for i in range(72) if (h >> i) & 1) for h in hexes.values()}
m6 = set(sat_weight_models(6, enumerate_models=True))
check("weight-6 stabilizers = exactly the 36 hexagons", m6 == hex_set)

dpair_set = set()
for g in base.elems:
    for d in D:
        v = hexes[g] ^ hexes[((g[0] + d[0]) % 6, (g[1] + d[1]) % 6)]
        dpair_set.add(frozenset(i for i in range(72) if (v >> i) & 1))
m10 = set(sat_weight_models(10, enumerate_models=True))
check("weight-10 stabilizers = exactly the 216 D-pairs", m10 == dpair_set)

# =========================================================================
print("\n=== AV4: Entry-5 foundations, exact ===")
# =========================================================================
def base_of(g):
    return (g[0] % 6, g[1])


def split_blocks(rows_cov, j):
    """Split cover rows into base-indexed sheet blocks S[(sc, sq)]."""
    def sheet(g):
        return 1 if ((g[0] - j) % 12) >= 6 else 0

    S = {(sc, sq): [0] * 36 for sc in (0, 1) for sq in (0, 1)}
    for gi, g in enumerate(cover.elems):
        sc, row, bi = sheet(g), rows_cov[gi], base.idx(base_of(g))
        for qi, q in enumerate(cover.elems):
            for blk in (0, 1):
                if (row >> (blk * 72 + qi)) & 1:
                    S[(sc, sheet(q))][bi] |= 1 << (blk * 36 + base.idx(base_of(q)))
    return S


cuts_ok, seam_ok = True, True
D2C_BY_CUT = []
for j in range(6):
    SX = split_blocks(HXc, j)
    SZ = split_blocks(HZc, j)
    cuts_ok &= (SX[(0, 0)] == SX[(1, 1)] and SX[(0, 1)] == SX[(1, 0)]
                and [a ^ b for a, b in zip(SX[(0, 0)], SX[(0, 1)])] == HXb)
    cuts_ok &= (SZ[(0, 0)] == SZ[(1, 1)] and SZ[(0, 1)] == SZ[(1, 0)]
                and [a ^ b for a, b in zip(SZ[(0, 0)], SZ[(0, 1)])] == HZb)
    d2c = SZ[(0, 1)]                    # column of face f = cross-sheet part
    D2C_BY_CUT.append(d2c)
    seam_ok &= all((d2c[f] & ~D2b[f]) == 0 for f in range(36))
check("block form [[nc,c],[c,nc]] with nc + c = base, H_X and H_Z, all 6 cuts",
      cuts_ok)
check("seam containment supp(d2c_j delta_g) subset h(g), ALL g and cuts", seam_ok)


def tau(u):
    v = 0
    for qi, q in enumerate(cover.elems):
        bi = base.idx(base_of(q))
        for blk in (0, 1):
            if (u >> (blk * 36 + bi)) & 1:
                v |= 1 << (blk * 72 + qi)
    return v


Z1b = nullspace(transpose_cols(HXb, 72))
check("dim Z1(base) = 42", len(Z1b) == 42)
kerd2b = nullspace(D2b)
check("dim ker d2(base) = 6 (H2)", len(kerd2b) == 6)
stab_basis = rref(D2b)
check("rank of base Z-stabilizers = 30", len(stab_basis) == 30)

lam_basis = nullspace(transpose_cols(D2b, 72))
check("dim left-annihilator of im d2(base) = 42", len(lam_basis) == 42)


def lift_functional(lam):
    r = 0
    for qi, q in enumerate(cover.elems):
        bi = base.idx(base_of(q))
        for blk in (0, 1):
            if (lam >> (blk * 36 + bi)) & 1:
                r |= 1 << (blk * 72 + qi)
    return r


danger_rows = HXc + [lift_functional(lam) for lam in lam_basis]
danger_vecs = nullspace(transpose_cols(danger_rows, 144))
check("dim dangerous-cycle space = 72", len(danger_vecs) == 72)

tauZ1 = [tau(u) for u in Z1b]
check("dangerous space == tau(Z1) + im(d2cov) (exact rref equality)",
      span_equal(rref(tauZ1 + D2c), rref(danger_vecs)))

U0 = []
for combo in nullspace(tauZ1 + D2c):
    u = 0
    for i in range(42):
        if (combo >> i) & 1:
            u ^= Z1b[i]
    U0.append(u)
U0_basis = rref(U0)
check("dim U0 = ker(tr_*) as cycle space = 36 (= Stab 30 + 6 Smith classes)",
      len(U0_basis) == 36)

bridge_ok = True
for j in range(6):
    reps = [apply_cols(D2C_BY_CUT[j], zeta) for zeta in kerd2b]
    cyc = all((HXb[c] & r).bit_count() % 2 == 0 for c in range(36) for r in reps)
    bridge_ok &= cyc and span_equal(rref(reps + D2b), U0_basis)
check("U0 = im(Delta_j) + Stab for EVERY cut (exactness + bridge, exact)",
      bridge_ok)

# =========================================================================
print("\n=== AV5: inversion duality Phi, re-derived ===")
# =========================================================================
def duality(bb, hx, hz):
    n = bb.n

    def phi(v):
        out = 0
        for qi, q in enumerate(bb.elems):
            iq = bb.idx(((-q[0]) % bb.xn, (-q[1]) % bb.yn))
            if (v >> qi) & 1:
                out |= 1 << (n + iq)
            if (v >> (n + qi)) & 1:
                out |= 1 << iq
        return out

    kerX = nullspace(transpose_cols(hx, 2 * n))
    kerZ = nullspace(transpose_cols(hz, 2 * n))
    ok = all((hz[r] & phi(v)).bit_count() % 2 == 0 for v in kerX for r in range(n))
    ok &= len(kerX) == len(kerZ)
    ok &= span_equal(rref([phi(r) for r in hz]), rref(hx))
    ok &= all(phi(v).bit_count() == v.bit_count() for v in kerX)
    return ok


check("base: Phi(ker H_X) = ker H_Z, Phi(Z-stabs) = X-stabs, weight-preserving",
      duality(base, HXb, HZb))
check("cover (gross): same", duality(cover, HXc, HZc))

# =========================================================================
print("\n=== AV6: CRT-frame shape-lemma intermediates (own frame) ===")
# =========================================================================
def f4mul(a, b):
    if a == 0 or b == 0:
        return 0
    return {0: 1, 1: 2, 2: 3}[({1: 0, 2: 1, 3: 2}[a] + {1: 0, 2: 1, 3: 2}[b]) % 3]


ORB = {1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}


def psi(j, t):
    c, d = ORB[j]
    return {0: 1, 1: 2, 2: 3}[(c * t[0] + d * t[1]) % 3]


def s_of(g):
    return (g[0] % 2) + 2 * (g[1] % 2)


def t_of(g):
    return (g[0] % 3, g[1] % 3)


def cell_of(s, t):
    return ((3 * (s & 1) + 4 * t[0]) % 6, (3 * (s >> 1) + 4 * t[1]) % 6)


def vhat(fvec, j):
    out = [0, 0, 0, 0]
    for i in range(36):
        if (fvec >> i) & 1:
            g = base.elems[i]
            out[s_of(g)] ^= psi(j, t_of(g))
    return tuple(out)


def parity_vec(fvec):
    out = [0, 0, 0, 0]
    for i in range(36):
        if (fvec >> i) & 1:
            out[s_of(base.elems[i])] ^= 1
    return tuple(out)


def ring_mul(f, g):
    out = [0, 0, 0, 0]
    for s1 in range(4):
        for s2 in range(4):
            out[s1 ^ s2] ^= f4mul(f[s1], g[s2])
    return tuple(out)


A_cols, B_cols = colA, colB
AHat = {j: vhat(A_cols[base.idx((0, 0))], j) for j in (1, 2, 3, 4)}
BHat = {j: vhat(B_cols[base.idx((0, 0))], j) for j in (1, 2, 3, 4)}

mult_ok = True
for gi in range(36):
    for j in (1, 2, 3, 4):
        zh = vhat(1 << gi, j)
        mult_ok &= vhat(A_cols[gi], j) == ring_mul(AHat[j], zh)
        mult_ok &= vhat(B_cols[gi], j) == ring_mul(BHat[j], zh)
check("transform multiplicativity (A and B, all 36 deltas, comps 1-4)", mult_ok)

eta = {j: psi(j, (0, 1)) for j in (1, 3, 4)}
check("Ahat_j = (1+eta, 1, eta, 0) for j in {1,3,4}; (eta1,eta3,eta4) = (w,w,w^2)",
      all(AHat[j] == ((1 ^ eta[j]), 1, eta[j], 0) for j in (1, 3, 4))
      and (eta[1], eta[3], eta[4]) == (2, 2, 3))

RING = list(product(range(4), repeat=4))
ONE = (1, 0, 0, 0)


def ideal_of(d):
    return {ring_mul(d, r) for r in RING}


ann_ok = True
for j, d in [(1, AHat[1]), (3, AHat[3]), (4, AHat[4]),
             (2, BHat[2]), (3, BHat[3]), (4, BHat[4])]:
    ann = {r for r in RING if ring_mul(d, r) == (0, 0, 0, 0)}
    ann_ok &= ann == ideal_of(d) and len(ann) == 16
unit_ok = (any(ring_mul(AHat[2], r) == ONE for r in RING)
           and any(ring_mul(BHat[1], r) == ONE for r in RING))
check("Ann(Ahat_j) = (Ahat_j) (radical comps, both sides); Ahat_2, Bhat_1 units",
      ann_ok and unit_ok)

eng_ok = True
for j in (1, 3, 4):
    for v in ideal_of(AHat[j]):
        nz = sum(1 for x in v if x)
        eng_ok &= nz in (0, 3, 4) and (nz != 4 or len(set(v)) == 1)
check("engine: nonzero ideal elements are constant (full) or co-point", eng_ok)

# d3(W) = min weight of nonzero f with Fourier support SUBSET of W;
# claimed to depend only on (#nontrivial orbits in W, trivial in W).
d3_by_W = {}
for mask in range(1, 512):
    cells = [(i // 3, i % 3) for i in range(9) if (mask >> i) & 1]
    s = set()
    if len(cells) % 2:
        s.add(0)
    for j in (1, 2, 3, 4):
        acc = 0
        for t in cells:
            acc ^= psi(j, t)
        if acc:
            s.add(j)
    fs = frozenset(s)
    for W in range(32):
        Wset = frozenset(j for j in range(5) if (W >> j) & 1)
        if fs <= Wset:
            d3_by_W[Wset] = min(d3_by_W.get(Wset, 99), len(cells))
sym_ok, d3 = True, {}
for Wset, m in d3_by_W.items():
    key = (len(Wset - {0}), 0 in Wset)
    if key in d3:
        sym_ok &= d3[key] == m
    d3[key] = m
check("d3 dictionary (support SUBSET W) matches the (n,eps) table AND the "
      "GL-symmetry holds over all 32 W",
      sym_ok and d3 == {(0, True): 9, (1, False): 6, (1, True): 3, (2, False): 4,
                        (2, True): 3, (3, False): 2, (3, True): 2, (4, False): 2,
                        (4, True): 1})

AnnA = nullspace(A_cols)
AnnB = nullspace(B_cols)
ker_set = set(span_iter(kerd2b))
check("dim Ann(A) = dim Ann(B) = 12; ker(d2) inside both",
      len(AnnA) == len(AnnB) == 12
      and all(in_span(rref(AnnA), v) for v in kerd2b)
      and all(in_span(rref(AnnB), v) for v in kerd2b))
annA_all = span_iter(AnnA)
wts = {v.bit_count() for v in annA_all if v}
check("Ann(A): min nonzero weight 6, all weights even",
      min(wts) == 6 and all(w % 2 == 0 for w in wts))
check("one-block exact min 16: |Bz'| on Ann(A)\\ker and |Az'| on Ann(B)\\ker",
      min(apply_cols(B_cols, z).bit_count()
          for z in annA_all if z not in ker_set) == 16
      and min(apply_cols(A_cols, z).bit_count()
              for z in span_iter(AnnB) if z not in ker_set) == 16)

solveA = make_solver(A_cols)
solveB = make_solver(B_cols)


def enum_shape(shape, solver):
    found = set()
    for layers in combinations(range(4), len(shape)):
        for ws in set(permutations(shape)):
            pools = [list(combinations(range(9), w)) for w in ws]
            for choice in product(*pools):
                f = 0
                for s, T in zip(layers, choice):
                    for ti in T:
                        f |= 1 << base.idx(cell_of(s, (ti // 3, ti % 3)))
                if solver(f) is not None:
                    found.add(f)
    return found


A111 = enum_shape((1, 1, 1), solveA)
check("(1,1,1) in im(A.) = exactly the 36 A.delta_g",
      A111 == set(A_cols) and len(A111) == 36)

A211 = enum_shape((2, 1, 1), solveA)
dApairsA = set()
for gi, g in enumerate(base.elems):
    for d in dA:
        z = (1 << gi) ^ (1 << base.idx(((g[0] + d[0]) % 6, (g[1] + d[1]) % 6)))
        dApairsA.add(apply_cols(A_cols, z))
check("(2,1,1) in im(A.) = exactly the 108 A.(dA-pair)",
      A211 == dApairsA and len(A211) == 108)
check("|B.(dA-pair)| = 6 (so the D-pair has |b| = 4 + 6 = 10)",
      {apply_cols(B_cols, (1 << base.idx((0, 0))) ^ (1 << base.idx(d))).bit_count()
       for d in dA} == {6})

check("(3,1,1): NO elements in im(A.) nor im(B.)",
      not enum_shape((3, 1, 1), solveA) and not enum_shape((3, 1, 1), solveB))

A2111 = enum_shape((2, 1, 1, 1), solveA)
z0 = solveA(next(iter(A2111)))
check("(2,1,1,1) in im(A.): exactly 36; completion min |Bz| = 9 (never 5)",
      len(A2111) == 36
      and min(apply_cols(B_cols, z0 ^ a).bit_count() for a in annA_all) == 9)

A221 = enum_shape((2, 2, 1), solveA)
fib_ok = True
for f in A221:
    cells = [base.elems[i] for i in range(36) if (f >> i) & 1]
    fib_ok &= len({c[0] % 3 for c in cells}) == 1     # single t_x value = t_y-fibre
mins221, seen = set(), set()
for f in A221:
    sizes = tuple(sum(1 for i in range(36) if (f >> i) & 1
                      and s_of(base.elems[i]) == s) for s in range(4))
    cls = sizes.index(1)
    if cls in seen:
        continue
    seen.add(cls)
    zf = solveA(f)
    mins221.add(min(apply_cols(B_cols, zf ^ a).bit_count() for a in annA_all))
check("(2,2,1) in im(A.): exactly 108, single t_y-fibre; completion min 9 "
      "(all 3 classes)", len(A221) == 108 and fib_ok and mins221 == {9})

A1111 = enum_shape((1, 1, 1, 1), solveA)
dcol_ok = all(len({t_of(base.elems[i]) for i in range(36) if (f >> i) & 1}) == 1
              for f in A1111)
zc = solveA(next(iter(A1111)))
check("(1,1,1,1) in im(A.) = the 9 delta-columns; completion min |Bz| = 12",
      len(A1111) == 9 and dcol_ok
      and min(apply_cols(B_cols, zc ^ a).bit_count() for a in annA_all) == 12)

end_ok = True
for d in [(0, 1), (3, 1), (3, 2)]:
    zp = (1 << base.idx((0, 0))) ^ (1 << base.idx(d))
    Bp = apply_cols(B_cols, zp)
    light = [a for a in annA_all
             if apply_cols(B_cols, zp ^ a).bit_count() <= 6]
    end_ok &= (len(light) == 64 and all(a in ker_set for a in light)
               and all(apply_cols(B_cols, zp ^ a) == Bp for a in light))
    end_ok &= min(apply_cols(B_cols, zp ^ a).bit_count()
                  for a in annA_all if a not in ker_set) >= 12
check("D-pair endgame: |Bz| <= 6 completions = the 64 kernel elts; "
      "non-kernel min >= 12 (3 classes)", end_ok)

kap_ok, n_dead2 = True, 0
NZ3 = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
for g in NZ3:
    for h in NZ3:
        if h == g or ((2 * g[0]) % 3, (2 * g[1]) % 3) == h:
            continue
        kap = {j: 1 ^ psi(j, g) ^ psi(j, h) for j in (1, 2, 3, 4)}
        dead = [j for j, v in kap.items() if v == 0]
        kap_ok &= len(dead) == 1
        if dead == [2]:
            n_dead2 += 1
            kap_ok &= f4mul(kap[1], kap[3]) != kap[4]
check(f"triangles: exactly one dead orbit each; all dead-2 cases (n={n_dead2}) "
      "violate kappa4 = kappa1*kappa3", kap_ok and n_dead2 > 0)


def pair_dirs(elems):
    dirs = set()
    for f in elems:
        for s in range(4):
            cells = [t_of(base.elems[i]) for i in range(36)
                     if (f >> i) & 1 and s_of(base.elems[i]) == s]
            if len(cells) == 2:
                a, b = cells
                dirs.add(((b[0] - a[0]) % 3, (b[1] - a[1]) % 3))
    return dirs


check("A-side weight-2 layers all run in the t_y direction",
      (pair_dirs(A211) | pair_dirs(A221) | pair_dirs(A2111)) <= {(0, 1), (0, 2)})
check("parity lemma: layer parities of A.delta = B.delta (all 36 => all z)",
      all(parity_vec(A_cols[gi]) == parity_vec(B_cols[gi]) for gi in range(36)))

print()
fails = [n for n, ok in RESULTS if not ok]
print(f"{'ALL CHECKS PASS' if not fails else 'FAILURES: ' + str(fails)} "
      f"({len(RESULTS)} checks)")

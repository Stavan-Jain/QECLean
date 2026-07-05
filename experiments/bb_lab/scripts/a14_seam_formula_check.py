"""A14 Phase 0 gate: Prop A14.1 numerics + seam-formula ground-truth check.

Verifies, per `notes/A14_safe_floor_criterion_plan.md` §6 Phase 0:

1. **pair72** ([[36,4,4]] on Z3xZ6 -> [[72,4,8]] on Z6xZ6, doubling x):
   the seam-carry formula reproduces the Lean `SeamTables.lean` literals
   bit-for-bit on the `MaskDefs` kernel basis; the three per-class coset
   minima are exactly 8 = 2*d(base) by direct 2^18 sweep; p2 = 0; delta2
   injective; im p1 = im delta2 (dim 2 = k/2); class-level G-transport
   `[seamC(g.zeta)] = g.[seamC(zeta)]` for every (g, zeta).
2. **gross base** ([[72,12,6]] on Z6xZ6 -> [[144,12,12]] on Z12xZ6):
   p2 = 0; delta2 injective (dim im delta2 = 6 = k/2); im p1 = im delta2;
   all 63 raw seam weights >= 12 (consistency with the proven MIm floor —
   screen S0 must not reject gross); y-orbit census of ker d2 \ 0 = 13
   (the MIm T_y-transport count) plus the full-G census; transport spot
   checks.
3. **CE2 negative control** (Z6xZ3 cover of Z3xZ3, A = 1+y+y^2,
   B = 1+x^2+x^4; (R) fails, k jumps 8 -> 16): p2 != 0, delta2 = 0, and
   im p1 is NOT contained in im delta2 — the (R) hypothesis of Prop A14.1
   is load-bearing.

Conventions (repo `BBChainComplex.lean`): d2(f) = (A*f, B*f) blocks,
d1(u,v) = B*u + A*v, conv(P,f)(h) = sum_x P(x) f(h-x); C1 layout is
block-major (block j, then row-major cell x*m+y); canonical section =
x-degree < ell; sheet 1 reads at x + ell; deck s = x^ell.

Run: `uv run python scripts/a14_seam_formula_check.py` from
`experiments/bb_lab/`.  Pure numpy; ~seconds.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from bb_lab.linalg import nullspace_f2, rank_f2  # noqa: E402

# ---------------------------------------------------------------- utilities


def idx(x: int, y: int, m: int) -> int:
    """Row-major cell index (matches the lab convention (x,y) -> x*m+y)."""
    return x * m + y


def conv_matrix(support: list[tuple[int, int]], l: int, m: int) -> np.ndarray:
    """Multiplication-by-P matrix on F2[Z_l x Z_m]: (P*f)(h) = sum P(x) f(h-x)."""
    n = l * m
    M = np.zeros((n, n), dtype=np.uint8)
    for (px, py) in support:
        for hx in range(l):
            for hy in range(m):
                M[idx(hx, hy, m), idx((hx - px) % l, (hy - py) % m, m)] ^= 1
    return M


def bb_matrices(A: list[tuple[int, int]], B: list[tuple[int, int]],
                l: int, m: int) -> tuple[np.ndarray, np.ndarray]:
    """(d2, d1) for the BB Koszul complex, repo block order.

    d2 : n -> 2n, block 0 = A*f, block 1 = B*f.
    d1 : 2n -> n, d1(u, v) = B*u + A*v.
    """
    cA, cB = conv_matrix(A, l, m), conv_matrix(B, l, m)
    d2 = np.vstack([cA, cB])
    d1 = np.hstack([cB, cA])
    return d2, d1


def dim_mod(S: np.ndarray, Bnd: np.ndarray) -> int:
    """dim of span(S rows) modulo span(Bnd rows)."""
    if S.shape[0] == 0:
        return 0
    return rank_f2(np.vstack([S, Bnd])) - rank_f2(Bnd)


def h1_dim(d2: np.ndarray, d1: np.ndarray) -> int:
    n2 = d1.shape[1]
    return (n2 - rank_f2(d1)) - rank_f2(d2)


class Cover:
    """Free Z2 BB cover doubling x: base Z_l x Z_m, cover Z_{2l} x Z_m."""

    def __init__(self, Ab, Bb, Ac, Bc, l, m):
        self.l, self.m = l, m
        self.nb, self.nc = l * m, 2 * l * m
        self.d2b, self.d1b = bb_matrices(Ab, Bb, l, m)
        self.d2c, self.d1c = bb_matrices(Ac, Bc, 2 * l, m)
        # sheet-0 lift on 2-chains (base cell -> cover cell, x < l)
        L = np.zeros((self.nc, self.nb), dtype=np.uint8)
        for x in range(l):
            for y in range(m):
                L[idx(x, y, m), idx(x, y, m)] = 1
        self.lift2 = L
        # fiber-sum pushforwards
        P0 = np.zeros((self.nb, self.nc), dtype=np.uint8)
        for x in range(2 * l):
            for y in range(m):
                P0[idx(x % l, y, m), idx(x, y, m)] ^= 1
        self.push0 = P0
        Z = np.zeros_like(P0)
        self.push1 = np.block([[P0, Z], [Z, P0]])

    def seam(self, zeta: np.ndarray) -> np.ndarray:
        """seamC(zeta): sheet-1 part of d2(cover) applied to the lifted 2-cycle."""
        t = (self.d2c @ (self.lift2 @ zeta)) & 1
        l, m, nb, nc = self.l, self.m, self.nb, self.nc
        out = np.zeros(2 * nb, dtype=np.uint8)
        for j in (0, 1):
            for x in range(l):
                for y in range(m):
                    out[j * nb + idx(x, y, m)] = t[j * nc + idx(x + l, y, m)]
        return out

    def translate2(self, g: tuple[int, int], zeta: np.ndarray) -> np.ndarray:
        """(g . zeta)(h) = zeta(h - g) on base 2-chains."""
        gx, gy = g
        out = np.zeros_like(zeta)
        for x in range(self.l):
            for y in range(self.m):
                out[idx(x, y, self.m)] = zeta[idx((x - gx) % self.l,
                                                  (y - gy) % self.m, self.m)]
        return out

    def translate1(self, g: tuple[int, int], c: np.ndarray) -> np.ndarray:
        """Diagonal translation on base 1-chains (both blocks)."""
        gx, gy = g
        out = np.zeros_like(c)
        for j in (0, 1):
            for x in range(self.l):
                for y in range(self.m):
                    out[j * self.nb + idx(x, y, self.m)] = \
                        c[j * self.nb + idx((x - gx) % self.l,
                                            (y - gy) % self.m, self.m)]
        return out


CHECKS: list[tuple[str, bool]] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    CHECKS.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))


# ---------------------------------------------------------------- pair72

print("== pair72: [[36,4,4]] on Z3xZ6 -> [[72,4,8]] on Z6xZ6 (doubling x) ==")

A36 = [(2, 0), (0, 1), (0, 3)]          # x^2 + y + y^3
B36 = [(0, 0), (1, 0), (0, 2)]          # 1 + x + y^2
p72 = Cover(A36, B36, A36, B36, l=3, m=6)

check("pair72 d1.d2 = 0 (base, cover)",
      not ((p72.d1b @ p72.d2b) & 1).any() and not ((p72.d1c @ p72.d2c) & 1).any())
kb, kc = h1_dim(p72.d2b, p72.d1b), h1_dim(p72.d2c, p72.d1c)
check("pair72 k(base) = k(cover) = 4 (R regime)", kb == 4 and kc == 4, f"k={kb}, k~={kc}")

# MaskDefs.lean systematic kernel basis
KB0 = [(0, 0), (0, 2), (0, 3), (0, 5), (1, 1), (1, 2), (1, 4), (1, 5),
       (2, 0), (2, 1), (2, 3), (2, 4)]
KB1 = [(0, 1), (0, 2), (0, 4), (0, 5), (1, 0), (1, 1), (1, 3), (1, 4),
       (2, 0), (2, 2), (2, 3), (2, 5)]
kb0 = np.zeros(18, dtype=np.uint8)
kb1 = np.zeros(18, dtype=np.uint8)
for (x, y) in KB0:
    kb0[idx(x, y, 6)] = 1
for (x, y) in KB1:
    kb1[idx(x, y, 6)] = 1
kerb = nullspace_f2(p72.d2b)
check("ker d2(base) dim = 2 = k/2; kb0,kb1 span it",
      kerb.shape[0] == 2
      and not ((p72.d2b @ kb0) & 1).any() and not ((p72.d2b @ kb1) & 1).any()
      and rank_f2(np.vstack([kb0, kb1])) == 2)

# SeamTables.lean literals (block j=0 = A-carry, j=1 = B-carry)
SEAMS = {
    (1, 0): ([(0, 1), (0, 2), (0, 4), (0, 5), (1, 0), (1, 1), (1, 3), (1, 4)],
             [(0, 0), (0, 1), (0, 3), (0, 4)]),
    (0, 1): ([(0, 0), (0, 1), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 5)],
             [(0, 0), (0, 2), (0, 3), (0, 5)]),
    (1, 1): ([(0, 0), (0, 2), (0, 3), (0, 5), (1, 1), (1, 2), (1, 4), (1, 5)],
             [(0, 1), (0, 2), (0, 4), (0, 5)]),
}


def literal_chain(cells0, cells1, nb, m):
    v = np.zeros(2 * nb, dtype=np.uint8)
    for (x, y) in cells0:
        v[idx(x, y, m)] = 1
    for (x, y) in cells1:
        v[nb + idx(x, y, m)] = 1
    return v


kcombo = {(1, 0): kb0, (0, 1): kb1, (1, 1): (kb0 ^ kb1)}
Bnd36 = p72.d2b.T  # rows generate im d2 (base boundaries)
for key, (c0, c1) in SEAMS.items():
    got = p72.seam(kcombo[key])
    want = literal_chain(c0, c1, 18, 6)
    check(f"seam-carry formula == SeamTables seam{key[0]}{key[1]} (bit-for-bit)",
          bool((got == want).all()), f"weight {int(got.sum())}")
    check(f"seam{key[0]}{key[1]} class nonzero (not a boundary)",
          dim_mod(got[None, :], Bnd36) == 1)

# per-class coset minima by direct 2^18 sweep
masks = np.arange(2 ** 18, dtype=np.uint32)
F = ((masks[:, None] >> np.arange(18)[None, :]) & 1).astype(np.uint8)
BND = (F @ p72.d2b.T.astype(np.uint16)) & 1  # (2^18, 36)
for key in SEAMS:
    w = (BND ^ p72.seam(kcombo[key])[None, :]).sum(axis=1)
    check(f"coset min of class {key} == 8 = 2*d(base)", int(w.min()) == 8,
          f"min {int(w.min())} at {int((w == w.min()).sum())} chains")

# Prop A14.1 (1)-(2) on pair72
ker2c = nullspace_f2(p72.d2c)
check("p2 = 0: every cover 2-cycle pushes to 0",
      ker2c.shape[0] == 2 and not ((ker2c @ p72.push0.T) & 1).any())
seam_rows = np.vstack([p72.seam(kb0), p72.seam(kb1)])
d_im_delta = dim_mod(seam_rows, Bnd36)
cyc_c = nullspace_f2(p72.d1c)
pushed = (cyc_c @ p72.push1.T) & 1
d_im_p1 = dim_mod(pushed, Bnd36)
d_union = dim_mod(np.vstack([pushed, seam_rows]), Bnd36)
check("delta2 injective: dim im delta2 = 2 = k/2", d_im_delta == 2)
check("im p1 = im delta2 (dims 2, union 2)",
      d_im_p1 == 2 and d_union == 2, f"im p1 {d_im_p1}, union {d_union}")

# class-level G-transport: [seamC(g.zeta)] = g.[seamC(zeta)] for all g, zeta
ok_transport = True
for gx in range(3):
    for gy in range(6):
        for z in kcombo.values():
            diff = p72.seam(p72.translate2((gx, gy), z)) ^ \
                p72.translate1((gx, gy), p72.seam(z))
            if dim_mod(diff[None, :], Bnd36) != 0:
                ok_transport = False
check("G-transport at class level (all 18 g x 3 classes)", ok_transport)

# ---------------------------------------------------------------- gross base

print("== gross: [[72,12,6]] on Z6xZ6 -> [[144,12,12]] on Z12xZ6 (doubling x) ==")

A72g = [(3, 0), (0, 1), (0, 2)]         # x^3 + y + y^2
B72g = [(0, 3), (1, 0), (2, 0)]         # y^3 + x + x^2
gr = Cover(A72g, B72g, A72g, B72g, l=6, m=6)

check("gross d1.d2 = 0 (base, cover)",
      not ((gr.d1b @ gr.d2b) & 1).any() and not ((gr.d1c @ gr.d2c) & 1).any())
kbg, kcg = h1_dim(gr.d2b, gr.d1b), h1_dim(gr.d2c, gr.d1c)
check("gross k(base) = k(cover) = 12 (R regime)", kbg == 12 and kcg == 12,
      f"k={kbg}, k~={kcg}")

kerg = nullspace_f2(gr.d2b)
check("gross ker d2(base) dim = 6 = k/2", kerg.shape[0] == 6)
ker2cg = nullspace_f2(gr.d2c)
check("gross p2 = 0: every cover 2-cycle pushes to 0",
      ker2cg.shape[0] == 6 and not ((ker2cg @ gr.push0.T) & 1).any())

Bnd72 = gr.d2b.T
seam_basis = np.vstack([gr.seam(kerg[i]) for i in range(6)])
d_delta_g = dim_mod(seam_basis, Bnd72)
cyc_cg = nullspace_f2(gr.d1c)
pushed_g = (cyc_cg @ gr.push1.T) & 1
d_p1_g = dim_mod(pushed_g, Bnd72)
d_union_g = dim_mod(np.vstack([pushed_g, seam_basis]), Bnd72)
check("gross delta2 injective: dim im delta2 = 6 = k/2", d_delta_g == 6)
check("gross im p1 = im delta2 (dims 6, union 6)",
      d_p1_g == 6 and d_union_g == 6, f"im p1 {d_p1_g}, union {d_union_g}")

# S0 on gross: all 63 raw seam weights (must be >= 12; MIm floor is proven)
weights = {}
elems = {}
for bits in range(1, 64):
    z = np.zeros(36, dtype=np.uint8)
    for i in range(6):
        if bits >> i & 1:
            z ^= kerg[i]
    elems[bits] = z
    weights[bits] = int(gr.seam(z).sum())
wmin = min(weights.values())
hist: dict[int, int] = {}
for w in weights.values():
    hist[w] = hist.get(w, 0) + 1
check("gross S0: all 63 raw seam weights >= 12 (screen must not reject gross)",
      wmin >= 12, f"min {wmin}, histogram {dict(sorted(hist.items()))}")

# orbit census of ker d2 \ 0 under y-translations and under full G
def orbit_count(translations) -> int:
    seen: set[bytes] = set()
    orbits = 0
    for bits, z in elems.items():
        if z.tobytes() in seen:
            continue
        orbits += 1
        for g in translations:
            seen.add(gr.translate2(g, z).tobytes())
    return orbits


y_orbits = orbit_count([(0, b) for b in range(6)])
g_orbits = orbit_count([(a, b) for a in range(6) for b in range(6)])
check("gross y-orbit census of 63 classes = 13 (MIm T_y-transport count)",
      y_orbits == 13, f"y-orbits {y_orbits}, full-G orbits {g_orbits}")

# transport spot checks at class level
rng = np.random.default_rng(14)
ok_g = True
for _ in range(20):
    g = (int(rng.integers(6)), int(rng.integers(6)))
    z = elems[int(rng.integers(1, 64))]
    diff = gr.seam(gr.translate2(g, z)) ^ gr.translate1(g, gr.seam(z))
    if dim_mod(diff[None, :], Bnd72) != 0:
        ok_g = False
check("gross G-transport at class level (20 random spot checks)", ok_g)

# ------------------------------------------------------- CE2 negative control

print("== CE2 control: Z6xZ3 cover of Z3xZ3, A = 1+y+y^2, B = 1+x^2+x^4 ==")

Ab_ce = [(0, 0), (0, 1), (0, 2)]        # 1 + y + y^2
Bb_ce = [(0, 0), (1, 0), (2, 0)]        # descends to 1 + x + x^2
Ac_ce = [(0, 0), (0, 1), (0, 2)]
Bc_ce = [(0, 0), (2, 0), (4, 0)]        # sector-pure lift: 1 + x^2 + x^4
ce = Cover(Ab_ce, Bb_ce, Ac_ce, Bc_ce, l=3, m=3)

check("CE2 d1.d2 = 0 (base, cover)",
      not ((ce.d1b @ ce.d2b) & 1).any() and not ((ce.d1c @ ce.d2c) & 1).any())
kb_ce, kc_ce = h1_dim(ce.d2b, ce.d1b), h1_dim(ce.d2c, ce.d1c)
check("CE2 k jumps 8 -> 16 ((R) fails)", kb_ce == 8 and kc_ce == 16,
      f"k={kb_ce}, k~={kc_ce}")

ker_ce = nullspace_f2(ce.d2b)
ker2c_ce = nullspace_f2(ce.d2c)
p2_nonzero = bool(((ker2c_ce @ ce.push0.T) & 1).any())
Bnd_ce = ce.d2b.T
seam_ce = np.vstack([ce.seam(ker_ce[i]) for i in range(ker_ce.shape[0])])
d_delta_ce = dim_mod(seam_ce, Bnd_ce)
cyc_ce = nullspace_f2(ce.d1c)
pushed_ce = (cyc_ce @ ce.push1.T) & 1
d_p1_ce = dim_mod(pushed_ce, Bnd_ce)
contained = dim_mod(np.vstack([pushed_ce, seam_ce]), Bnd_ce) == d_delta_ce
check("CE2 p2 != 0 (Prop A14.1(1) hypothesis load-bearing)", p2_nonzero)
check("CE2 delta2 = 0 (im delta2 dim 0; vs dim H2(base) = 4)",
      d_delta_ce == 0 and ker_ce.shape[0] == 4,
      f"dim im delta2 {d_delta_ce}, dim H2 {ker_ce.shape[0]}")
check("CE2 linchpin FAILS: im p1 not contained in im delta2",
      d_p1_ce > 0 and not contained, f"dim im p1 {d_p1_ce}")

# ---------------------------------------------------------------- summary

fails = [n for n, ok in CHECKS if not ok]
print(f"\n{len(CHECKS) - len(fails)}/{len(CHECKS)} checks passed.")
if fails:
    print("FAILED:")
    for n in fails:
        print(f"  - {n}")
    sys.exit(1)
print("ALL CHECKS PASS — A14 Phase 0 gate green.")

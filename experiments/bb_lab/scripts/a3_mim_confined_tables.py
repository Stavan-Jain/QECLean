"""A3 / Track 1.1 Entry 23 — O1 structure: the confined floor as a spine C-table.

Re-coordinatizes the Entry-22 confined floor so it can be evaluated by
hand, and computes the candidate C-tables.

Coordinates (T1).  In R = F4[Z2^2] write X = 1 + s_x, Y = 1 + s_y,
XY = (1+s_x)(1+s_y) = Sigma_g g.  Then X^2 = Y^2 = 0, rad R =
F4 X + F4 Y + F4 XY, and for any aug-0 element nu not in F4 XY:
nu^2 = 0, im(nu .) = F4 nu + F4 XY (16 elements).  Claims verified:
  - rho1 = X + w Y + w^2 XY, rho2 = w X + Y + w^2 XY (w = omega);
  - Gamma_3 = {(a Bhat3 + beta XY, a Ahat3 + alpha XY) : a, beta, alpha
    in F4} (the graph ideal is free in the two XY-shifts);
  - Gamma_4 = {(w(a Ahat4 + g XY), a Ahat4 + g XY)} (Bhat4 = w Ahat4);
  - comp-0 data: V0L = V0R =: V0 ranges over ALL of F2[Z2^2] (16).

So a confined-floor configuration is exactly:

    V0 (16, shared) | spine (a3, a4) in F4^2 (shared) | gamma (4, shared
    XY-shift of comp 4, with the w-twist between blocks) | independent
    XY-shifts beta, alpha of comp 3 per block | confined V2L = c2 +
    p2 rho2 + q2 XY, V1R = c1 + p1 rho1 + q1 XY.

and the floor decomposes over the 16 spine cells (T3):

    FLOOR = min over (a3, a4) of  m(a3, a4),
    m = min over shared (V0, gamma) of [ Lmin(V0, a3, a4, gamma)
                                       + Rmin(V0, a3, a4, gamma) ],

with Lmin a min over (beta, p2, q2) of a 4-slot M1-table sum and Rmin
over (alpha, p1, q1) of an M2 sum.  The 16-cell m-tables per orbit are
the candidate C-tables for the hand write-up.

Sections:
  T1  the basis change and all constants in XY-coordinates; the
      Gamma-parametrizations verified; per-orbit offsets and pins.
  T2  the M1/M2 tables: censuses; the swap symmetry M2 from M1; the
      symmetry group (9 translations x Frobenius) orbit count on cells;
      the M1 <= 2 cell classification (point / pair rigidity).
  T3  the spine C-tables: m(a3, a4) per orbit (exact, = the confined
      floor when minimized); also the fully-marginal bound
      min(l + r) for comparison, and the coarse (aliveness-only)
      per-cell bound to see which cells need fine values.
  T4  achiever accounting at the floor cells: the per-slot M-values of
      a minimizing configuration (the "1+1+1"-style cost breakdown).
  T5  symmetry compression: the translation stabilizer of each coset,
      its action on the spine; negation/Frobenius closure.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cmb = bb_check_matrices(Ab, Bb)
d2b = (cmb.H_Z & 1).T
nb = 36

A_steps = [(3, 0), (0, 1), (0, 2)]
B_steps = [(0, 3), (1, 0), (2, 0)]


def d2c_mat(j):
    d2c = np.zeros((72, nb), np.uint8)
    for g in Gb:
        col = Gb.index(g)
        for blk, steps in ((0, B_steps), (1, A_steps)):
            for (sx, sy) in steps:
                if ((g[0] - j) % 6) + sx >= 6:
                    cell = blk * nb + Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6))
                    d2c[cell, col] ^= 1
    return d2c


D2C0 = d2c_mat(0)
ker2 = nullspace_f2(d2b)


def span_elems(rows):
    out = []
    for mask in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (mask >> i) & 1:
                v ^= rows[i]
        out.append(v)
    return out


Z2all = [z for z in span_elems(ker2) if z.any()]


def translate36(z, dx, dy):
    out = np.zeros_like(z)
    for g in Gb:
        out[Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = z[Gb.index(g)]
    return out


def swap36(z):
    out = np.zeros_like(z)
    for g in Gb:
        out[Gb.index((g[1], g[0]))] = z[Gb.index(g)]
    return out


orbs = {}
for z in Z2all:
    cands = []
    for dx in range(6):
        for dy in range(6):
            t = translate36(z, dx, dy)
            cands.append(t.tobytes())
            cands.append(swap36(t).tobytes())
    orbs.setdefault(min(cands), []).append(z)
ORBKEYS = sorted(orbs, key=lambda k: (int(np.frombuffer(k, np.uint8).sum()),
                                      len(orbs[k])))
ONAME = {}
for key in ORBKEYS:
    z = np.frombuffer(key, np.uint8)
    ONAME[key] = f"wt-{int(z.sum())}(n={len(orbs[key])})"

F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        F4_MUL[a, b_] = ((a0 & b0) ^ (a1 & b1)) | \
            ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))

ORBITS5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, 2, 3]
W = 2


def f4m(a, b):
    return int(F4_MUL[a, b])


def comp_hat(vec36, j):
    out = [0, 0, 0, 0]
    c, d = ORBITS5[j]
    for g in Gb:
        if vec36[Gb.index(g)]:
            s = (g[0] % 2) | ((g[1] % 2) << 1)
            out[s] ^= WPOW[(c * (g[0] % 3) + d * (g[1] % 3)) % 3]
    return tuple(out)


def ring_mul4(f, g):
    out = [0, 0, 0, 0]
    for s1 in range(4):
        if f[s1]:
            for s2 in range(4):
                if g[s2]:
                    out[s1 ^ s2] ^= f4m(f[s1], g[s2])
    return tuple(out)


def xor4(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def smul(lam, v):
    return tuple(f4m(lam, x) for x in v)


delta0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
AH = {j: comp_hat((d2b[nb:, :] @ delta0) % 2, j) for j in range(5)}
BH = {j: comp_hat((d2b[:nb, :] @ delta0) % 2, j) for j in range(5)}
ALL_F4 = [tuple(t) for t in product(range(4), repeat=4)]
ALL_F2 = [e for e in ALL_F4 if all(c in (0, 1) for c in e)]


def comp_offsets(w72):
    return {j: (comp_hat(w72[:nb], j), comp_hat(w72[nb:], j)) for j in range(5)}


def inv4(u):
    return next(t for t in ALL_F4 if ring_mul4(u, t) == (1, 0, 0, 0))


# slot-coordinate constants
E1 = (1, 0, 0, 0)
SX = (0, 1, 0, 0)
SY = (0, 0, 1, 0)
SXY = (0, 0, 0, 1)
Xr = xor4(E1, SX)                  # X = 1 + s_x
Yr = xor4(E1, SY)
XYr = ring_mul4(Xr, Yr)            # = (1,1,1,1)


def in_xy_basis(v):
    """v = a*1 + b*X + c*Y + d*XY: invert the triangular change of basis."""
    # 1 = e; X = e + s_x; Y = e + s_y; XY = e + s_x + s_y + s_xy
    d = v[3]
    c = v[2] ^ d
    b = v[1] ^ d
    a = v[0] ^ b ^ c ^ d
    return (a, b, c, d)


NAMES4 = {0: "0", 1: "1", 2: "w", 3: "w2"}


def fmt_xy(v):
    a, b, c, d = in_xy_basis(v)
    parts = []
    for coef, sym in ((a, "1"), (b, "X"), (c, "Y"), (d, "XY")):
        if coef:
            parts.append(("" if coef == 1 else NAMES4[coef] + "*") + sym)
    return " + ".join(parts) if parts else "0"


print("=== T1: constants in the XY basis ===")
rho1 = ring_mul4(AH[1], inv4(BH[1]))
rho2 = ring_mul4(BH[2], inv4(AH[2]))
print(f"  Ahat1 = {fmt_xy(AH[1])};  Bhat1 = {fmt_xy(BH[1])}")
print(f"  Ahat2 = {fmt_xy(AH[2])};  Bhat2 = {fmt_xy(BH[2])}")
print(f"  Ahat3 = {fmt_xy(AH[3])};  Bhat3 = {fmt_xy(BH[3])}")
print(f"  Ahat4 = {fmt_xy(AH[4])};  Bhat4 = {fmt_xy(BH[4])}")
print(f"  rho1 = {fmt_xy(rho1)} (claim X + w Y + w2 XY): "
      f"{rho1 == xor4(xor4(Xr, smul(W, Yr)), smul(3, XYr))}")
print(f"  rho2 = {fmt_xy(rho2)} (claim w X + Y + w2 XY): "
      f"{rho2 == xor4(xor4(smul(W, Xr), Yr), smul(3, XYr))}")
im_r1 = sorted({ring_mul4(rho1, t) for t in ALL_F4})
ok_im = set(im_r1) == {xor4(smul(p, rho1), smul(q, XYr))
                       for p in range(4) for q in range(4)}
print(f"  im rho1 == F4 rho1 + F4 XY: {ok_im}")
# Gamma_3 parametrization
G3 = {(ring_mul4(BH[3], t), ring_mul4(AH[3], t)) for t in ALL_F4}
G3p = {(xor4(smul(a, BH[3]), smul(be, XYr)), xor4(smul(a, AH[3]), smul(al, XYr)))
       for a in range(4) for be in range(4) for al in range(4)}
print(f"  Gamma_3 == {{(a Bhat3 + beta XY, a Ahat3 + alpha XY)}}: {G3 == G3p} "
      f"(sizes {len(G3)}, {len(G3p)})")
G4 = {(ring_mul4(BH[4], t), ring_mul4(AH[4], t)) for t in ALL_F4}
G4p = {(smul(W, xor4(smul(a, AH[4]), smul(g, XYr))),
        xor4(smul(a, AH[4]), smul(g, XYr))) for a in range(4) for g in range(4)}
print(f"  Gamma_4 == {{(w(a Ahat4 + g XY), a Ahat4 + g XY)}}: {G4 == G4p} "
      f"(sizes {len(G4)}, {len(G4p)})")

ORB_DATA = {}
print("\n  per-orbit offsets (XY basis) and constants:")
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C0 @ zrep) % 2
    offs = comp_offsets(w0)
    c1 = xor4(offs[1][1], ring_mul4(rho1, offs[1][0]))
    c2 = xor4(offs[2][0], ring_mul4(rho2, offs[2][1]))
    ORB_DATA[key] = (offs, c1, c2)
    print(f"  {ONAME[key]}:")
    print(f"    off3 = (L: {fmt_xy(offs[3][0])} | R: {fmt_xy(offs[3][1])})")
    print(f"    off4 = (L: {fmt_xy(offs[4][0])} | R: {fmt_xy(offs[4][1])})")
    print(f"    c1 = {fmt_xy(c1)};  c2 = {fmt_xy(c2)}")

# =========================================================================
print("\n=== T2: the M-tables ===")
WT = np.full((2, 4, 4, 4, 4), -1, np.int8)
for fb in range(512):
    vals = []
    for j, (c, d) in ORBITS5.items():
        acc = 0
        for t1 in range(3):
            for t2 in range(3):
                if (fb >> (3 * t1 + t2)) & 1:
                    acc ^= WPOW[(c * t1 + d * t2) % 3]
        vals.append(acc)
    WT[vals[0], vals[1], vals[2], vals[3], vals[4]] = bin(fb).count("1")
M1 = WT.min(axis=1)                       # [v0, v2, v3, v4]
M2 = WT.min(axis=2)                       # [v0, v1, v3, v4]
cen1 = {}
for v0 in range(2):
    for a in range(4):
        for b_ in range(4):
            for c in range(4):
                cen1[int(M1[v0, a, b_, c])] = cen1.get(int(M1[v0, a, b_, c]), 0) + 1
print(f"  M1 cell census {{value: cells}}: {dict(sorted(cen1.items()))}")
FROB = [0, 1, 3, 2]                       # squaring on F4
cands = {
    "M2(v0,a,b,c) == M1(v0,a,b,c)":
        all(M2[v0, a, b_, c] == M1[v0, a, b_, c]
            for v0 in range(2) for a in range(4) for b_ in range(4)
            for c in range(4)),
    "M2(v0,a,b,c) == M1(v0,F(a),F(b),F(c)) (Frobenius all)":
        all(M2[v0, a, b_, c] == M1[v0, FROB[a], FROB[b_], FROB[c]]
            for v0 in range(2) for a in range(4) for b_ in range(4)
            for c in range(4)),
    "M2(v0,a,b,c) == M1(v0,a,b,F(c)) (swap: Frobenius on comp 4 only)":
        all(M2[v0, a, b_, c] == M1[v0, a, b_, FROB[c]]
            for v0 in range(2) for a in range(4) for b_ in range(4)
            for c in range(4)),
}
for k, v in cands.items():
    print(f"  {k}: {v}")
# symmetry orbits of M1 cells under 9 translations x Frobenius
TRANS_SCAL = []
for r1 in range(3):
    for r2 in range(3):
        # chi_j(r) for j = 2, 3, 4 with (c,d) = (1,0), (1,1), (1,2)
        TRANS_SCAL.append((WPOW[r1 % 3], WPOW[(r1 + r2) % 3],
                           WPOW[(r1 + 2 * r2) % 3]))
orbits_cells = {}
for v0 in range(2):
    for a in range(4):
        for b_ in range(4):
            for c in range(4):
                reps = []
                for (s2, s3, s4) in TRANS_SCAL:
                    t = (v0, f4m(s2, a), f4m(s3, b_), f4m(s4, c))
                    reps.append(t)
                    reps.append((v0, FROB[f4m(s2, a)], FROB[f4m(s3, b_)],
                                 FROB[f4m(s4, c)]))
                orbits_cells.setdefault(min(reps), []).append((v0, a, b_, c))
print(f"  M1 cells: 128 -> {len(orbits_cells)} orbits under "
      f"(9 translations) x Frobenius")
for rep, cells in sorted(orbits_cells.items()):
    v = int(M1[rep])
    print(f"    rep (v0,v2,v3,v4) = {rep}: M1 = {v}, orbit size {len(cells)}")

# =========================================================================
print("\n=== T3: the spine C-tables m(a3, a4) per orbit ===")
F2_16 = ALL_F2                            # the 16 V0 values


def slot_vals(base, shift):
    return tuple(base[s] ^ shift for s in range(4))


def cell_m(key, a3, a4, coarse=False):
    """m(a3, a4): exact min over shared (V0, gamma) of Lmin + Rmin."""
    offs, c1, c2 = ORB_DATA[key]
    b3L = xor4(offs[3][0], smul(a3, BH[3]))
    b3R = xor4(offs[3][1], smul(a3, AH[3]))
    b4 = xor4(offs[4][1], smul(a4, AH[4]))     # R-side base; L = off4L + w(...)
    b4L_core = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
    best = 10 ** 9
    for g in range(4):
        V4R = xor4(b4, smul(g, XYr))
        V4L = xor4(b4L_core, smul(f4m(W, g), XYr))
        for V0 in F2_16:
            # L block: min over beta, V2L in c2 + p rho2 + q XY
            lmin = 10 ** 9
            for be in range(4):
                V3L = xor4(b3L, smul(be, XYr))
                for p in range(4):
                    base2 = xor4(c2, smul(p, rho2))
                    for q in range(4):
                        V2L = xor4(base2, smul(q, XYr))
                        tot = sum(int(M1[V0[s], V2L[s], V3L[s], V4L[s]])
                                  for s in range(4))
                        lmin = min(lmin, tot)
            rmin = 10 ** 9
            for al in range(4):
                V3R = xor4(b3R, smul(al, XYr))
                for p in range(4):
                    base1 = xor4(c1, smul(p, rho1))
                    for q in range(4):
                        V1R = xor4(base1, smul(q, XYr))
                        tot = sum(int(M2[V0[s], V1R[s], V3R[s], V4R[s]])
                                  for s in range(4))
                        rmin = min(rmin, tot)
            best = min(best, lmin + rmin)
    return best


def block_min(key, a3, a4, block, V0=None, g=None, witness=False):
    """min over the block's own knobs of the 4-slot M-sum; V0 / gamma
    fixed if given, else minimized over (the unlinked relaxation)."""
    offs, c1, c2 = ORB_DATA[key]
    Mtab = M1 if block == 0 else M2
    rho = rho2 if block == 0 else rho1
    if block == 0:
        b3 = xor4(offs[3][0], smul(a3, BH[3]))
        b4core = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
    else:
        b3 = xor4(offs[3][1], smul(a3, AH[3]))
        b4core = xor4(offs[4][1], smul(a4, AH[4]))
    best, arg = 10 ** 9, None
    for V0c in ([V0] if V0 is not None else F2_16):
        for gc in ([g] if g is not None else range(4)):
            gs = f4m(W, gc) if block == 0 else gc
            V4 = xor4(b4core, smul(gs, XYr))
            for sh in range(4):
                V3 = xor4(b3, smul(sh, XYr))
                for p in range(4):
                    for q in range(4):
                        Vc = xor4(smul(p, rho), smul(q, XYr))
                        tot = sum(int(Mtab[V0c[s], Vc[s], V3[s], V4[s]])
                                  for s in range(4))
                        if tot < best:
                            best = tot
                            arg = (V0c, gc, sh, (p, q), V3, V4, Vc)
    return (best, arg) if witness else best


for key in ORBKEYS:
    print(f"\n  {ONAME[key]}: m(a3, a4) grid (rows a3 = 0,1,w,w2; "
          f"cols a4 = 0,1,w,w2):")
    grid = np.zeros((4, 4), int)
    for a3 in range(4):
        for a4 in range(4):
            grid[a3, a4] = cell_m(key, a3, a4)
    for a3 in range(4):
        print("    " + "  ".join(f"{grid[a3, a4]:2d}" for a4 in range(4)))
    print(f"    floor = {grid.min()} (Entry-22 confined floor cross-check)")
    # unlinked per-block tables
    gl = np.zeros((4, 4), int)
    gr = np.zeros((4, 4), int)
    for a3 in range(4):
        for a4 in range(4):
            gl[a3, a4] = block_min(key, a3, a4, 0)
            gr[a3, a4] = block_min(key, a3, a4, 1)
    print("    unlinked L-table / R-table / L+R:")
    for a3 in range(4):
        print("      " + "  ".join(f"{gl[a3, a4]:2d}" for a4 in range(4))
              + "   |   " + "  ".join(f"{gr[a3, a4]:2d}" for a4 in range(4))
              + "   |   " + "  ".join(f"{gl[a3, a4] + gr[a3, a4]:2d}"
                                      for a4 in range(4)))
    print(f"    unlinked floor = {(gl + gr).min()} vs linked {grid.min()}")

# =========================================================================
print("\n=== T4: achiever accounting at extremal cells ===")
for key in ORBKEYS:
    grid = {}
    for a3 in range(4):
        for a4 in range(4):
            grid[(a3, a4)] = cell_m(key, a3, a4)
    fl = min(grid.values())
    cells = sorted(c for c, v in grid.items() if v == fl)
    print(f"\n  {ONAME[key]}: floor {fl} at spine cells {cells}")
    a3, a4 = cells[0]
    # joint witness at the first floor cell: redo the shared minimization
    offs, c1, c2 = ORB_DATA[key]
    best = (10 ** 9, None)
    for gc in range(4):
        for V0c in F2_16:
            lb, la = block_min(key, a3, a4, 0, V0=V0c, g=gc, witness=True)
            rb, ra = block_min(key, a3, a4, 1, V0=V0c, g=gc, witness=True)
            if lb + rb < best[0]:
                best = (lb + rb, (V0c, gc, la, ra))
    tot, (V0c, gc, la, ra) = best
    _, _, shL, pqL, V3L, V4L, V2L = la
    _, _, shR, pqR, V3R, V4R, V1R = ra
    lrow = [int(M1[V0c[s], V2L[s], V3L[s], V4L[s]]) for s in range(4)]
    rrow = [int(M2[V0c[s], V1R[s], V3R[s], V4R[s]]) for s in range(4)]
    print(f"    witness at {cells[0]}: V0 = {V0c}, gamma = {gc}")
    print(f"      L slots (V2L,V3L,V4L) = {V2L}, {V3L}, {V4L}; "
          f"M1 row {lrow} (sum {sum(lrow)})")
    print(f"      R slots (V1R,V3R,V4R) = {V1R}, {V3R}, {V4R}; "
          f"M2 row {rrow} (sum {sum(rrow)})")

# =========================================================================
print("\n=== T5: symmetry compression of the spine ===")
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    stab = [(dx, dy) for dx in range(6) for dy in range(6)
            if (translate36(zrep, dx, dy) == zrep).all()]
    print(f"  {ONAME[key]}: translation stabilizer order {len(stab)}: {stab}")

# =========================================================================
print("\n=== T6: the support+parity relaxation — where slope-kills are needed ===")
# Per slot the value-blind cost given (v0, alive-pattern of (v2,v3,v4)):
#   v0=0: 0 alive -> 0; 1 -> 4; 2 -> 2; 3 -> 2   (loci assumed available)
#   v0=1: anything -> 3, except 3-alive -> 1     (delta locus assumed)
# Support-class lemma (kill-multiset form): for v = c 1 + alpha X +
# beta Y + delta XY with delta free, the slot values are
# (c+alpha+beta+delta, alpha+delta, beta+delta, delta), so the zero set
# at a given delta is {s : kill[s] = delta} with the KILL VECTOR
# kill = (c+alpha+beta, alpha, beta, 0); the support options are the
# complements of the level sets of kill.


def support_options(v):
    a, al, be, _ = in_xy_basis(v)
    kill = (a ^ al ^ be, al, be, 0)
    return sorted({frozenset(s for s in range(4) if kill[s] != d)
                   for d in range(4)})


def relaxed_block_min(key, a3, a4, block):
    offs, c1, c2 = ORB_DATA[key]
    rho = rho2 if block == 0 else rho1
    if block == 0:
        base3 = xor4(offs[3][0], smul(a3, BH[3]))
        base4 = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
    else:
        base3 = xor4(offs[3][1], smul(a3, AH[3]))
        base4 = xor4(offs[4][1], smul(a4, AH[4]))
    # comp-2/1 confined side: p rho + q XY -> for p != 0 the kill vector
    # of rho applies (four distinct entries: co-points only); p = 0 gives
    # the empty and full supports (q XY)
    opts2 = sorted(set(support_options(rho))
                   | {frozenset(), frozenset(range(4))})
    opts3 = support_options(base3)
    opts4 = support_options(base4)
    best = 10 ** 9
    arg = None
    for S2 in opts2:
        for S3 in opts3:
            for S4 in opts4:
                for V0m in range(16):
                    tot = 0
                    for s in range(4):
                        n = (s in S2) + (s in S3) + (s in S4)
                        if (V0m >> s) & 1:
                            tot += 1 if n == 3 else 3
                        else:
                            tot += (0, 4, 2, 2)[n]
                    if tot < best:
                        best, arg = tot, (S2, S3, S4, V0m)
    return best, arg


for key in ORBKEYS:
    print(f"\n  {ONAME[key]}: relaxed block tables (L | R), gap to true:")
    for a3 in range(4):
        rowL, rowR = [], []
        for a4 in range(4):
            bl, _ = relaxed_block_min(key, a3, a4, 0)
            br, _ = relaxed_block_min(key, a3, a4, 1)
            tl = block_min(key, a3, a4, 0)
            tr = block_min(key, a3, a4, 1)
            rowL.append(f"{bl}/{tl}")
            rowR.append(f"{br}/{tr}")
        print("    " + "  ".join(f"{x:>4}" for x in rowL) + "   |   "
              + "  ".join(f"{x:>4}" for x in rowR))

print("\nDone.")

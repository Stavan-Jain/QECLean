"""A3 / Track 1.1 Entry 25 — O2: the weight-10 kill at the floor-10 cells.

After O1 (Entries 23-24): every Smith-coset element w has weight >=
m(spine(w)) >= 10, with m >= 12 on the wt-24 orbits and on the 12-cells
of wt-16/18a/18b.  Weights are even, so the only obstruction left to
(M-im) is a coset element of weight EXACTLY 10 sitting at a floor-10
spine cell.  Such a w must:

  (i)   realize an engine-10 achiever configuration: shared (V0, gamma),
        spine cell (a3, a4) with m = 10, per-block data (V2L in im rho2,
        d3L | V1R in im rho1, d3R) with cost_L + cost_R = 10, every slot
        AT its M-value (any slack is >= +4 by the fibre gap, pushing
        |w| >= 14);
  (ii)  have per-slot free-side values in the MINIMIZER sets:
        v1L(s) in argmin M1(...), v2R(s) in argmin M2(...);
  (iii) satisfy the two links dropped by the confined floor:
        rho1 V1L = V1R   and   rho2 V2R = V2L
        (c1 = c2 = 0; solution sets are cosets of ker rho1 = F4 Ahat1 +
        F4 XY resp. ker rho2 = F4 Ahat2' + F4 XY, 16 elements each).

This script enumerates ALL achievers at ALL floor-10 cells of the three
orbits and checks (ii) + (iii): for every achiever, at least one link
coset misses the minimizer product.  Expected (Entries 20/21 verified
the endpoint twice): every achiever is killed -> no weight-10 elements
-> (M-im) holds on all five orbits.

Discovery/validation only; the load-bearing argument is the engine
lemmas + the per-achiever-family link computations (to be written up).
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
ONAME = {k: f"wt-{int(np.frombuffer(k, np.uint8).sum())}(n={len(orbs[k])})"
         for k in ORBKEYS}

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


def inv4(u):
    return next(t for t in ALL_F4 if ring_mul4(u, t) == (1, 0, 0, 0))


XYr = (1, 1, 1, 1)
rho1 = ring_mul4(AH[1], inv4(BH[1]))
rho2 = ring_mul4(BH[2], inv4(AH[2]))
IMR1 = sorted({ring_mul4(rho1, t) for t in ALL_F4})
IMR2 = sorted({ring_mul4(rho2, t) for t in ALL_F4})
KER1 = [t for t in ALL_F4 if ring_mul4(rho1, t) == (0, 0, 0, 0)]
KER2 = [t for t in ALL_F4 if ring_mul4(rho2, t) == (0, 0, 0, 0)]
assert len(KER1) == 16 and len(KER2) == 16

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
M1 = WT.min(axis=1)
M2 = WT.min(axis=2)

ORB_DATA = {}
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C0 @ zrep) % 2
    ORB_DATA[key] = {j: (comp_hat(w0[:nb], j), comp_hat(w0[nb:], j))
                     for j in range(5)}

print("=== O2: the weight-10 kill at the floor-10 cells ===")
GRAND_OK = True
for key in ORBKEYS[:3]:
    offs = ORB_DATA[key]
    total_ach = 0
    killed = 0
    k1_only = k2_only = both_fail = 0
    exemplar_shown = False
    cells10 = []
    for a3 in range(4):
        for a4 in range(4):
            b3L = xor4(offs[3][0], smul(a3, BH[3]))
            b3R = xor4(offs[3][1], smul(a3, AH[3]))
            b4Lc = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
            b4Rc = xor4(offs[4][1], smul(a4, AH[4]))
            cell_ach = []
            for gamma in range(4):
                V4L = xor4(b4Lc, smul(f4m(W, gamma), XYr))
                V4R = xor4(b4Rc, smul(gamma, XYr))
                for V0 in ALL_F2:
                    # all L-configs with cost, all R-configs with cost
                    Ls = []
                    for d3 in range(4):
                        V3 = xor4(b3L, smul(d3, XYr))
                        for V2 in IMR2:
                            c = sum(int(M1[V0[s], V2[s], V3[s], V4L[s]])
                                    for s in range(4))
                            if c <= 10:
                                Ls.append((c, V3, V2))
                    Rs = []
                    for d3 in range(4):
                        V3 = xor4(b3R, smul(d3, XYr))
                        for V1 in IMR1:
                            c = sum(int(M2[V0[s], V1[s], V3[s], V4R[s]])
                                    for s in range(4))
                            if c <= 10:
                                Rs.append((c, V3, V1))
                    for cL, V3L, V2L in Ls:
                        for cR, V3R, V1R in Rs:
                            if cL + cR == 10:
                                cell_ach.append((V0, gamma, V3L, V2L, V4L,
                                                 V3R, V1R, V4R))
            if cell_ach:
                cells10.append(((a3, a4), len(cell_ach)))
            for (V0, gamma, V3L, V2L, V4L, V3R, V1R, V4R) in cell_ach:
                total_ach += 1
                # minimizer sets per slot
                min1 = []
                for s in range(4):
                    mv = int(M1[V0[s], V2L[s], V3L[s], V4L[s]])
                    min1.append([v1 for v1 in range(4)
                                 if int(WT[V0[s], v1, V2L[s], V3L[s],
                                           V4L[s]]) == mv])
                min2 = []
                for s in range(4):
                    mv = int(M2[V0[s], V1R[s], V3R[s], V4R[s]])
                    min2.append([v2 for v2 in range(4)
                                 if int(WT[V0[s], V1R[s], v2, V3R[s],
                                           V4R[s]]) == mv])
                # link 1: rho1 V1L = V1R with V1L in prod(min1)
                t0 = next(t for t in ALL_F4 if ring_mul4(rho1, t) == V1R)
                ok1 = any(all(xor4(t0, k)[s] in min1[s] for s in range(4))
                          for k in KER1)
                # link 2: rho2 V2R = V2L with V2R in prod(min2)
                u0 = next(t for t in ALL_F4 if ring_mul4(rho2, t) == V2L)
                ok2 = any(all(xor4(u0, k)[s] in min2[s] for s in range(4))
                          for k in KER2)
                if not (ok1 and ok2):
                    killed += 1
                    if not ok1 and ok2:
                        k1_only += 1
                    elif ok1 and not ok2:
                        k2_only += 1
                    else:
                        both_fail += 1
                    if not exemplar_shown:
                        print(f"  exemplar killed achiever at {ONAME[key]} "
                              f"cell ({a3},{a4}):")
                        print(f"    V0 = {V0}, gamma = {gamma}")
                        print(f"    L: V2L = {V2L}, V3L = {V3L}, V4L = {V4L}; "
                              f"v1L minimizer sets {min1}")
                        print(f"    R: V1R = {V1R}, V3R = {V3R}, V4R = {V4R}; "
                              f"v2R minimizer sets {min2}")
                        print(f"    link-1 solvable: {ok1}; link-2 solvable: "
                              f"{ok2}")
                        exemplar_shown = True
                else:
                    print(f"  !! SURVIVOR at {ONAME[key]}: V0={V0}, "
                          f"gamma={gamma}, V2L={V2L}, V1R={V1R}")
    ok = (killed == total_ach)
    GRAND_OK &= ok
    print(f"\n  {ONAME[key]}: floor-10 cells with achievers: {cells10}")
    print(f"    achievers {total_ach}; killed {killed} "
          f"(link-1 fails only: {k1_only}, link-2 only: {k2_only}, "
          f"both: {both_fail}) -> weight-10 impossible: {ok}")

print(f"\n  VERDICT — every floor-10 achiever violates a rho-link, all three "
      f"orbits: {GRAND_OK}")
print("  (with O1 this gives min |C(zeta)| >= 12 on ALL five orbits: (M-im))")

print("\nDone.")

"""A3 / Track 1.1 Entry 17 — (R) by an explicit homotopy; (M-im) discovery.

(R): ker delta = im Delta.  Hand proof found: over the cover ring
F2[Z12 x Z6], squaring B kills its y-dependence (y^6 = 1):

    B^2 = y^6 + x^2 + x^4 = 1 + x^2 + x^4,   and
    (1 + x^2)(1 + x^2 + x^4) = 1 + x^6,

so for ANY cover 1-cycle v = (v_L, v_R) (A v_L = B v_R) the 2-chain
z := (1+x^2) B v_L satisfies

    d2 z = (B z, A z) = ((1+x^2)B^2 v_L, (1+x^2)B A v_L)
         = ((1+x^6) v_L, (1+x^2)B^2 v_R) = (1+x^6)(v_L, v_R) = v + sigma(v).

Hence (1 + sigma) Z1(cover) subset B1(cover): sigma_* = id on H1(gross),
tau_* pr_* = (1+sigma)_* = 0, so im pr_* subset ker tau_* = im Delta, and
equality follows from rank-nullity (both = 12 - dim im tau_*).  Checks:

  R1  the two polynomial identities over F2[Z12 x Z6];
  R2  d2(z) = (1+x^6) v for every element of a basis of ker H_X^cov
      (78 vectors), i.e. the homotopy works on the whole cycle space;
  R3  the same homotopy on the BASE ring (x^6 = 1): z = (1+x^2)B v_L gives
      d2 z = 0 — consistency (the base statement is vacuous, as it must be).

(M-im) discovery — dist(d2c_j zeta, Stab_Z) >= 12 for zeta in ker d2 \\ 0:

  M1  orbit classification of the 63 nonzero zeta under translation (36)
      and the x<->y swap; weights per orbit.
  M2  per orbit rep: |d2c_j zeta| for all cuts j; the exact pi_x-collapse
      bound L_j (min over t in F2[Z6] of |c_{j+4} + y^3 t| +
      |c_{j+3}+c_{j+4}+c_{j+5} + (1+y+y^2) t|, c_i = column profiles of
      zeta) — does the cheap collapse bound ever reach 12?
  M3  the tau-criterion: for each weight-6 logical orbit rep u, tau(u) is
      NOT a cover boundary (rank test) — verifies [u] not in im Delta,
      the weight-6 sub-rung of (M-im), and consistency with T4/S7.
  M4  the Smith linking form: P[xi, zeta] = <d1c_j^T xi, d2c_j zeta> for
      xi in ker H_X^T (6) x zeta in ker d2 basis (6); rank over F2 and
      cut-dependence.  Nondegeneracy would give a detector route to
      (M-im) lower bounds.
  M5  structure of the minimum reps: the zeta with |d2c_0 zeta| = 12 —
      orbit membership, layer/fibre profile of the weight-12 cycles.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import combinations

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, rank_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cmb = bb_check_matrices(Ab, Bb)
HX = (cmb.H_X & 1)
d2b = (cmb.H_Z & 1).T
nb = 36

Gc = ZmZn(12, 6)
Ac = Poly.from_string("x^3 + y + y^2", Gc)
Bc = Poly.from_string("y^3 + x + x^2", Gc)
cmc = bb_check_matrices(Ac, Bc)
HXc = (cmc.H_X & 1)
d2c_cov = (cmc.H_Z & 1).T
nc_ = 72

def conv(G, f, g):
    out = {}
    for a in f:
        for b in g:
            c = G.add(a, b)
            out[c] = out.get(c, 0) ^ 1
    return {c for c, v in out.items() if v}

# ------------------------------------------------------ R1: the identities
print("=== R1: the homotopy identities over F2[Z12 x Z6] ===")
Bset = {(0, 3), (1, 0), (2, 0)}
B2 = conv(Gc, Bset, Bset)
print(f"  B^2 = {sorted(B2)} (claim {{(0,0), (2,0), (4,0)}} = 1 + x^2 + x^4)")
eps = conv(Gc, {(0, 0), (2, 0)}, B2)
print(f"  (1+x^2) * B^2 = {sorted(eps)} (claim {{(0,0), (6,0)}} = 1 + x^6)")

# ---------------------------------------------------- R2: the whole kernel
print("\n=== R2: d2((1+x^2) B v_L) = (1 + sigma) v on a basis of ker H_X^cov ===")
TB = np.zeros((nc_, nc_), np.uint8)               # mult by (1+x^2)B on F2[Gc]
for g in Gc:
    for m in conv(Gc, {(0, 0), (2, 0)}, Bset):
        TB[Gc.index(Gc.add(g, m)), Gc.index(g)] ^= 1
SIG = np.zeros((nc_, nc_), np.uint8)              # mult by x^6
for g in Gc:
    SIG[Gc.index(Gc.add(g, (6, 0))), Gc.index(g)] = 1
kerc = nullspace_f2(HXc)
print(f"  dim ker H_X^cov = {kerc.shape[0]} (claim 78)")
ok_r2 = True
for v in kerc:
    vL, vR = v[:nc_], v[nc_:]
    z = (TB @ vL) % 2
    bz = (d2c_cov @ z) % 2                         # (B z, A z)
    tgt = np.concatenate([(vL ^ (SIG @ vL) % 2), (vR ^ (SIG @ vR) % 2)]) % 2
    ok_r2 &= (bz == tgt).all()
print(f"  homotopy identity holds on all basis cycles: {ok_r2}")

# --------------------------------------------------------- R3: base sanity
print("\n=== R3: base-ring consistency ((1+x^2)B^2 = 1+x^6 = 0 on Z6) ===")
B2b = conv(Gb, {(0, 3), (1, 0), (2, 0)}, {(0, 3), (1, 0), (2, 0)})
epsb = conv(Gb, {(0, 0), (2, 0)}, B2b)
print(f"  over F2[Z6^2]: (1+x^2)B^2 = {sorted(epsb)} (claim empty = 0)")

# ------------------------------------------------------- M1: zeta orbits
print("\n=== M1: orbits of ker d2 \\ 0 under translation + swap ===")
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
print(f"  orbits: {len(orbs)}; (size, weight) per orbit: "
      f"{sorted((len(v), int(np.frombuffer(k, dtype=np.uint8).sum())) for k, v in orbs.items())}")

# --------------------------------------- M2: rep weights + collapse bound
print("\n=== M2: |d2c_j zeta| and the pi_x-collapse bound per orbit ===")
B_steps = [(0, 3), (1, 0), (2, 0)]
A_steps = [(3, 0), (0, 1), (0, 2)]
def split_d2_apply(j, z):
    out_c = np.zeros(72, np.uint8)
    for g in Gb:
        if not z[Gb.index(g)]:
            continue
        for blk, steps in ((0, B_steps), (1, A_steps)):
            for (sx, sy) in steps:
                if ((g[0] - j) % 6) + sx >= 6:
                    out_c[blk * nb + Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6))] ^= 1
    return out_c
def wt6(v):
    return bin(v).count("1")
def Lbound(z, j):
    cols = [int("".join(str(z[Gb.index((i, y))]) for y in range(6)), 2) for i in range(6)]
    def ymul(poly_shifts, c):
        out = 0
        for sh in poly_shifts:
            # multiply column (6-bit, index = y) by y^sh: rotate bits
            r = 0
            for y in range(6):
                if (c >> (5 - y)) & 1:
                    r ^= 1 << (5 - ((y + sh) % 6))
            out ^= r
        return out
    c4 = cols[(j + 4) % 6]
    c345 = cols[(j + 3) % 6] ^ cols[(j + 4) % 6] ^ cols[(j + 5) % 6]
    best = 99
    for t in range(64):
        a = wt6(c4 ^ ymul([3], t))
        b = wt6(c345 ^ ymul([0, 1, 2], t))
        best = min(best, a + b)
    return best
for k in sorted(orbs):
    z = np.frombuffer(k, dtype=np.uint8).copy()
    dws = [int(split_d2_apply(j, z).sum()) for j in range(6)]
    lbs = [Lbound(z, j) for j in range(6)]
    print(f"  orbit wt {int(z.sum())}: |d2c_j zeta| = {dws}; collapse L_j = {lbs} "
          f"(max {max(lbs)})")

# ----------------------------------------------------- M3: tau criterion
print("\n=== M3: tau(u) is NOT a cover boundary for weight-6 logicals ===")
def tau_lift(w):
    v = np.zeros(2 * nc_, np.uint8)
    for blk in range(2):
        for g in Gb:
            if w[blk * nb + Gb.index(g)]:
                v[blk * nc_ + Gc.index((g[0], g[1]))] ^= 1
                v[blk * nc_ + Gc.index((g[0] + 6, g[1]))] ^= 1
    return v
AnnA = nullspace_f2(d2b[nb:, :])
zA6 = next(z for z in span_elems(AnnA) if z.sum() == 6)
u6 = np.zeros(72, np.uint8); u6[:nb] = zA6
rank_d2cov = rank_f2(d2c_cov.T)
ok_m3 = rank_f2(np.vstack([d2c_cov.T, tau_lift(u6)])) > rank_d2cov
print(f"  Ann(A)-type weight-6 logical: tau(u) not in im d2^cov: {ok_m3} "
      f"(=> [u] not in im Delta)")

# --------------------------------------------------- M4: the linking form
print("\n=== M4: the Smith linking form <d1c^T xi, d2c zeta> ===")
A_steps_d1 = [(3, 0), (0, 1), (0, 2)]
B_steps_d1 = [(0, 3), (1, 0), (2, 0)]
def d1c_mat(j):
    d1c = np.zeros((nb, 2 * nb), np.uint8)
    for blk, steps in ((0, A_steps_d1), (1, B_steps_d1)):
        for g in Gb:
            col = blk * nb + Gb.index(g)
            for (sx, sy) in steps:
                if ((g[0] - j) % 6) + sx >= 6:
                    d1c[Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6)), col] ^= 1
    return d1c
K0 = nullspace_f2(HX.T)                            # ker H_X^T: 6
ranks = []
for j in range(6):
    d1c = d1c_mat(j)
    P = np.zeros((K0.shape[0], ker2.shape[0]), np.uint8)
    for a, xi in enumerate(K0):
        for b, zr in enumerate(ker2):
            wvec = split_d2_apply(j, zr)
            P[a, b] = int(xi @ ((d1c @ wvec) % 2)) % 2
    ranks.append(rank_f2(P))
print(f"  rank of the 6x6 linking form per cut j: {ranks} "
      f"(nondegenerate iff 6)")

# ------------------------------------------- M5: the weight-12 minimum reps
print("\n=== M6: seam-flux functionals on the weight-6 logical orbits ===")
# [w] in im Delta  <=>  xi^T d1c_j w = 0 for all xi in ker H_X^T (M4: the
# linking form vanishes, so im Delta^X = (im Delta^Z)^perp).  The weight-6
# sub-rung of (M-im) is: every weight-6 logical has a NONZERO flux.
d1c0 = d1c_mat(0)
AnnB = nullspace_f2(d2b[:nb, :])
zB6 = next(z for z in span_elems(AnnB) if z.sum() == 6)
u6B = np.zeros(72, np.uint8); u6B[nb:] = zB6
# the 12-orbit mixed rep: a (3,3)-split weight-6 cycle that is not a hexagon
mixed = None
hexes = {tuple(np.flatnonzero((d2b @ np.eye(nb, dtype=np.uint8)[i]) % 2))
         for i in range(nb)}
def cols_int(M):
    return [int("".join(str(b) for b in M[:, i]), 2) for i in range(M.shape[1])]
MAi, MBi = cols_int(HX[:, :nb]), cols_int(HX[:, nb:])
from itertools import combinations as combs
synA = {}
for T in combs(range(nb), 3):
    s = MAi[T[0]] ^ MAi[T[1]] ^ MAi[T[2]]
    synA.setdefault(s, []).append(T)
for T in combs(range(nb), 3):
    s = MBi[T[0]] ^ MBi[T[1]] ^ MBi[T[2]]
    if s in synA:
        for TL in synA[s]:
            cells = tuple(sorted(TL + tuple(nb + i for i in T)))
            if cells not in hexes:
                mixed = np.zeros(72, np.uint8)
                for i in cells:
                    mixed[i] = 1
                break
        if mixed is not None:
            break
for name, u in (("Ann(A)-type", u6), ("Ann(B)-type", u6B), ("mixed (3,3)", mixed)):
    flux = [int(xi @ ((d1c0 @ u) % 2)) % 2 for xi in K0]
    print(f"  {name}: flux vector {flux} (nonzero: {any(flux)})")

print("\n=== M5: which zeta give |d2c_0 zeta| = 12, and their structure ===")
n12 = 0
fibre_flags = []
for z in Z2all:
    w = split_d2_apply(0, z)
    if int(w.sum()) == 12:
        n12 += 1
        cells_L = [(g[0], g[1]) for g in Gb if w[Gb.index(g)]]
        cells_R = [(g[0], g[1]) for g in Gb if w[nb + Gb.index(g)]]
        txL = {x % 3 for (x, y) in cells_L}
        txR = {x % 3 for (x, y) in cells_R}
        fibre_flags.append((len(txL), len(txR),
                            int(z.sum()), len(cells_L), len(cells_R)))
print(f"  count with |d2c_0 zeta| = 12: {n12} (S8 said 18)")
print(f"  (t_x-fibres L, t_x-fibres R, |zeta|, |w_L|, |w_R|) multiset: "
      f"{sorted(set(fibre_flags))}")

# ---------------------- M7: the winding sharpening + pinned components
print("\n=== M7: d1c.d2c = 0 = d1nc.d2nc (the no-double-wrap identities) ===")
def d2_mats(j):
    d2nc = np.zeros((72, nb), np.uint8)
    d2c = np.zeros((72, nb), np.uint8)
    for g in Gb:
        col = Gb.index(g)
        for blk, steps in ((0, B_steps), (1, A_steps)):
            for (sx, sy) in steps:
                cell = blk * nb + Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6))
                tgt = d2c if ((g[0] - j) % 6) + sx >= 6 else d2nc
                tgt[cell, col] ^= 1
    return d2nc, d2c
ok_m7 = True
for j in range(6):
    d1c = d1c_mat(j)
    d1nc = (HX ^ d1c) % 2
    d2nc, d2c_ = d2_mats(j)
    ok_m7 &= not ((d1c @ d2c_) % 2).any()
    ok_m7 &= not ((d1nc @ d2nc) % 2).any()
    ok_m7 &= not (((d1nc @ d2c_) % 2) ^ ((d1c @ d2nc) % 2)).any()
print(f"  d1c_j d2c_j = 0, d1nc_j d2nc_j = 0, d1nc d2c = d1c d2nc (all j): {ok_m7}")

print("\n=== M8: pinned components of the Smith cosets (affine-COST seed) ===")
# per orbit rep zeta and component j: is the offset pair ((d2c z)^L_j-hat,
# (d2c z)^R_j-hat) realizable as (Bhat t, Ahat t)?  Non-realizable = pinned.
ORBITS5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
def wpow(k): return [1, 2, 3][k % 3]
F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        F4_MUL[a, b_] = ((a0 & b0) ^ (a1 & b1)) | ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))
def f4m(a, b): return int(F4_MUL[a, b])
def comp_hat(vec36, j):
    out = [0, 0, 0, 0]
    for g in Gb:
        if vec36[Gb.index(g)]:
            s = (g[0] % 2) | ((g[1] % 2) << 1)
            c, d = ORBITS5[j]
            out[s] ^= wpow(c * (g[0] % 3) + d * (g[1] % 3))
    return tuple(out)
def ring_mul4(f, g):
    out = [0, 0, 0, 0]
    for s1 in range(4):
        for s2 in range(4):
            out[s1 ^ s2] ^= f4m(f[s1], g[s2])
    return tuple(out)
delta0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
AH = {j: comp_hat((d2b[nb:, :] @ delta0) % 2, j) for j in range(5)}
BH = {j: comp_hat((d2b[:nb, :] @ delta0) % 2, j) for j in range(5)}
def all_elems4():
    from itertools import product as prod
    return [tuple(t) for t in prod(range(4), repeat=4)]
S4 = all_elems4()
realizable = {j: {(ring_mul4(BH[j], t), ring_mul4(AH[j], t)) for t in S4} for j in range(5)}
for k in sorted(orbs):
    z = np.frombuffer(k, dtype=np.uint8).copy()
    w0 = split_d2_apply(0, z)
    pins = []
    for j in range(5):
        off = (comp_hat(w0[:nb], j), comp_hat(w0[nb:], j))
        pins.append(0 if off in realizable[j] else 1)
    print(f"  orbit wt {int(z.sum())}: pinned components (j=0..4): {pins}")

print("\nDone.")

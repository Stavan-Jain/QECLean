"""A3 / Track 1.1 Entry 22 — hand-organization of (M-im), part I.

Verifies each step of the hand lemmas that replace pieces of the Entry-20
machine closure, and probes the structure of what remains (the combo
classification and the completion kill), exactly as Entries 10-12 did for
the (M) classification.

Hand lemmas verified here (proofs in the log entry):
  H1 (slot parity)        wt(f) == fhat(triv) = v0 (mod 2) for every layer
                          f in F2[Z3^2] — augmentation.
  H2 (2-cycle evenness)   zeta in ker d2 = Ann(A) cap Ann(B); A zeta = 0
                          gives the column relation c_{i+3} = (y+y^2) c_i,
                          and |(y+y^2) c| is even, so EVERY COLUMN of zeta
                          has even weight; rows mirror via B zeta = 0.
  H3 (even coset weight)  the cut-0 Smith rep has block parities
                          |L| == |P4 zeta|, |R| == |P3|+|P4|+|P5| (mod 2),
                          both 0 by H2; |d2 t| is even; so every element
                          of every Smith coset has even weight, and (with
                          H1) even VCOST: the sub-12 world is costs
                          {6, 8, 10} and weights {6, 8, 10}.
  H4 (value rigidity)     E(v) = 1 exactly at the 9 delta-point value
                          tuples (1, psi_1(p), ..., psi_4(p)); E(v) = 2
                          exactly at the 36 point-pair tuples (v0 = 0,
                          exactly one dead nontrivial component — the
                          direction of p - q); these are the dictionary
                          backbone cells.
  H5 (affine rigidity)    on every Smith coset, ALL FOUR nontrivial
                          components are affine graphs: V1R, V2L as
                          before (rho_1 = Ahat_1 Bhat_1^{-1} etc.); at
                          comp 3 the pair (V3L, V3R) is a graph over
                          V3L (ker Bhat_3 = the joint kernel); at comp 4
                          Bhat_4 = omega Ahat_4 forces the LINEAR
                          relation V4L + off4L = omega (V4R + off4R).
                          Also rho_1, rho_2 are radical with rho^2 != 0,
                          rho^3 = 0.

  H8 (fibre gap)          in every (v0, v3, v4; a1, a2)-fibre of the
                          value table, every non-minimal weight is
                          >= min + 4 (66 nontrivial fibres, all gaps
                          exactly 4): a non-minimizing slot costs +4.

Probes for the remaining two lemmas (statistics, not proofs):
  H6 (combo families)     coarse-signature counts of the cost-<=10 combos
                          per orbit (how many families would a hand
                          classification need?).
  H7 (kill localization)  per combo, the minimum completion weight and
                          the per-slot deficit pattern (E_actual - d3v) of
                          a minimal completion — where the >= 4 slack
                          concentrates; cross-tab of cost vs minimum
                          completion weight; the aug-locks aug(c1) =
                          aug(c2) = 0 on every orbit.
  H10 (confined floor)    the floor with the rho-confinements V1R in
                          c1 + im rho1, V2L in c2 + im rho2 (16 vectors
                          each) taken value-exactly and the free sides
                          v1L, v2R relaxed per slot: 10/10/10/12/12 —
                          the two wt-24 orbits close at the floor; the
                          other three reduce to killing weight EXACTLY 10
                          (weights are even).

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
HX = (cmb.H_X & 1)
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


D2C = {j: d2c_mat(j) for j in range(6)}
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

F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        F4_MUL[a, b_] = ((a0 & b0) ^ (a1 & b1)) | \
            ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))

ORBITS5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, 2, 3]


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
                    out[s1 ^ s2] ^= int(F4_MUL[f[s1], g[s2]])
    return tuple(out)


def xor4(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def mask_of(e):
    return sum(1 << s for s in range(4) if e[s])


delta0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
AH = {j: comp_hat((d2b[nb:, :] @ delta0) % 2, j) for j in range(5)}
BH = {j: comp_hat((d2b[:nb, :] @ delta0) % 2, j) for j in range(5)}

ALL_F4 = [tuple(t) for t in product(range(4), repeat=4)]
ALL_F2 = [e for e in ALL_F4 if all(c in (0, 1) for c in e)]


def comp_offsets(w72):
    return {j: (comp_hat(w72[:nb], j), comp_hat(w72[nb:], j)) for j in range(5)}


def coset_pairs(offs, j):
    offL, offR = offs[j]
    dom = ALL_F2 if j == 0 else ALL_F4
    out = {}
    for t in dom:
        out[(xor4(offL, ring_mul4(BH[j], t)),
             xor4(offR, ring_mul4(AH[j], t)))] = True
    return list(out)


def offset_patterns(offs, j):
    return sorted({(mask_of(vL), mask_of(vR)) for vL, vR in coset_pairs(offs, j)})


WT_OF_VAL = np.full((2, 4, 4, 4, 4), -1, np.int8)
for fb in range(512):
    vals = []
    for j, (c, d) in ORBITS5.items():
        acc = 0
        for t1 in range(3):
            for t2 in range(3):
                if (fb >> (3 * t1 + t2)) & 1:
                    acc ^= WPOW[(c * t1 + d * t2) % 3]
        vals.append(acc)
    WT_OF_VAL[vals[0], vals[1], vals[2], vals[3], vals[4]] = bin(fb).count("1")

D3V = np.full((32, 4), 99, np.int8)
for v0 in range(2):
    for v3 in range(4):
        for v4 in range(4):
            for a1 in range(2):
                for a2 in range(2):
                    dom1 = (0,) if a1 == 0 else (1, 2, 3)
                    dom2 = (0,) if a2 == 0 else (1, 2, 3)
                    D3V[v0 * 16 + v3 * 4 + v4, a1 + 2 * a2] = \
                        min(int(WT_OF_VAL[v0, v1, v2, v3, v4])
                            for v1 in dom1 for v2 in dom2)

# =========================================================================
print("=== H1: slot parity — wt(f) == v0 (mod 2) for all 512 layers ===")
ok_h1 = True
for v0 in range(2):
    for v1 in range(4):
        for v2 in range(4):
            for v3 in range(4):
                for v4 in range(4):
                    ok_h1 &= (int(WT_OF_VAL[v0, v1, v2, v3, v4]) % 2 == v0)
print(f"  PASS: {ok_h1}")

# =========================================================================
print("\n=== H2: 2-cycle evenness — columns and rows of zeta are even ===")
ok_cols = ok_rows = ok_rel = True
YY = {(0, 1), (0, 2)}                       # y + y^2 as shifts


def col_vec(z, i):
    return np.array([z[Gb.index((i, y))] for y in range(6)], np.uint8)


for z in Z2all:
    for i in range(6):
        ok_cols &= (int(col_vec(z, i).sum()) % 2 == 0)
        ok_rows &= (int(sum(z[Gb.index((x, i))] for x in range(6))) % 2 == 0)
        # the column relation c_{i+3} = (y + y^2) c_i
        lhs = col_vec(z, (i + 3) % 6)
        rhs = np.zeros(6, np.uint8)
        for y in range(6):
            if z[Gb.index((i, y))]:
                rhs[(y + 1) % 6] ^= 1
                rhs[(y + 2) % 6] ^= 1
        ok_rel &= (lhs == rhs).all()
print(f"  all columns even: {ok_cols}; all rows even: {ok_rows}; "
      f"c_(i+3) = (y+y^2) c_i: {ok_rel}")

# =========================================================================
print("\n=== H3: block parities of the Smith reps; even coset weight ===")
ok_h3 = True
for z in Z2all:
    w0 = (D2C[0] @ z) % 2
    P4 = sum(int(z[Gb.index((4, y))]) for y in range(6))
    P345 = sum(int(z[Gb.index((x, y))]) for x in (3, 4, 5) for y in range(6))
    ok_h3 &= (int(w0[:nb].sum()) % 2 == P4 % 2)
    ok_h3 &= (int(w0[nb:].sum()) % 2 == P345 % 2)
    ok_h3 &= (int(w0.sum()) % 2 == 0)
print(f"  |L| == |P4 zeta|, |R| == |P3+P4+P5 zeta| (mod 2), |w0| even: {ok_h3}")

# =========================================================================
print("\n=== H4: the E <= 2 value-rigidity cells ===")
pts = []
for p1 in range(3):
    for p2 in range(3):
        v = (1,) + tuple(WPOW[(c * p1 + d * p2) % 3]
                         for j, (c, d) in ORBITS5.items() if j > 0)
        pts.append(v)
e1 = {tuple(int(x) for x in np.argwhere(WT_OF_VAL == 1)[k])
      for k in range(int((WT_OF_VAL == 1).sum()))}
print(f"  E = 1 cells: {len(e1)} (claim 9); equal to the point evaluations: "
      f"{e1 == set(pts)}")
pairs = set()
for i in range(9):
    for k in range(i + 1, 9):
        pairs.add(tuple(a ^ b for a, b in zip(pts[i], pts[k])))
e2 = {tuple(int(x) for x in np.argwhere(WT_OF_VAL == 2)[k])
      for k in range(int((WT_OF_VAL == 2).sum()))}
ok_dead = all(v[0] == 0 and sum(1 for j in (1, 2, 3, 4) if v[j] == 0) == 1
              for v in e2)
print(f"  E = 2 cells: {len(e2)} (claim 36); equal to the point-pair sums: "
      f"{e2 == pairs}; v0 = 0 with exactly one dead nontrivial comp: {ok_dead}")
print(f"  E = 3 cells: {int((WT_OF_VAL == 3).sum())} (for reference)")

# =========================================================================
print("\n=== H5: affine rigidity of all four nontrivial components ===")


def inv4(u):
    return next(t for t in ALL_F4 if ring_mul4(u, t) == (1, 0, 0, 0))


rho1 = ring_mul4(AH[1], inv4(BH[1]))
rho2 = ring_mul4(BH[2], inv4(AH[2]))
r1sq = ring_mul4(rho1, rho1)
r2sq = ring_mul4(rho2, rho2)
print(f"  rho1 = {rho1}, rho1^2 = {r1sq}, rho1^3 = {ring_mul4(r1sq, rho1)} "
      f"(claim nilpotent of order 3)")
print(f"  rho2 = {rho2}, rho2^2 = {r2sq}, rho2^3 = {ring_mul4(r2sq, rho2)}")
# comp 3: the pair is a graph over the L-value
g3 = {}
ok_g3 = True
for t in ALL_F4:
    x, y = ring_mul4(BH[3], t), ring_mul4(AH[3], t)
    if x in g3 and g3[x] != y:
        ok_g3 = False
    g3[x] = y
print(f"  comp 3: (Bhat_3 t, Ahat_3 t) is a graph over the first entry "
      f"(|im Bhat_3| = {len(g3)}): {ok_g3}")
# comp 4: Bhat_4 = omega * Ahat_4 (or omega^2) — find the scalar
scal = None
for w_ in (2, 3):
    if all(int(F4_MUL[w_, AH[4][s]]) == BH[4][s] for s in range(4)):
        scal = w_
print(f"  comp 4: Bhat_4 = omega^k Ahat_4 with omega^k = {scal} "
      f"(claim: a nonzero scalar)")

# =========================================================================
print("\n=== H8: the fibre-gap lemma — non-minimal slots cost >= +4 ===")
gap_hist = {}
ok_h8 = True
for v0 in range(2):
    for v3 in range(4):
        for v4 in range(4):
            for a1 in range(2):
                for a2 in range(2):
                    dom1 = (0,) if a1 == 0 else (1, 2, 3)
                    dom2 = (0,) if a2 == 0 else (1, 2, 3)
                    ws = sorted(int(WT_OF_VAL[v0, v1, v2, v3, v4])
                                for v1 in dom1 for v2 in dom2)
                    dist = sorted(set(ws))
                    if len(dist) > 1:
                        gap_hist[dist[1] - dist[0]] = \
                            gap_hist.get(dist[1] - dist[0], 0) + 1
                    ok_h8 &= all(w == ws[0] or w >= ws[0] + 4 for w in ws)
print(f"  second-min gaps histogram: {dict(sorted(gap_hist.items()))}")
print(f"  every non-minimal weight >= fibre min + 4: {ok_h8}")

# =========================================================================
# Entry-20 floor machinery (combos + completions), reused for the probes
NE_CHUNK = 4096


def vfloor_combos(offs, collect_max=10):
    cos0 = coset_pairs(offs, 0)
    cos3 = coset_pairs(offs, 3)
    cos4 = coset_pairs(offs, 4)
    g1 = offset_patterns(offs, 1)
    g2 = offset_patterns(offs, 2)
    n0, n3, n4 = len(cos0), len(cos3), len(cos4)
    V = {(c, b): np.array([[pair[b][s] for s in range(4)] for pair in cos],
                          dtype=np.int32)
         for c, cos in ((0, cos0), (3, cos3), (4, cos4)) for b in (0, 1)}
    I0, I3, I4 = np.meshgrid(np.arange(n0), np.arange(n3), np.arange(n4),
                             indexing="ij")
    I0, I3, I4 = I0.ravel(), I3.ravel(), I4.ravel()
    NE = len(I0)
    idxE = np.empty((NE, 2, 4), np.int32)
    for b in (0, 1):
        for s in range(4):
            idxE[:, b, s] = (V[(0, b)][I0, s] * 16 + V[(3, b)][I3, s] * 4 +
                             V[(4, b)][I4, s])
    P = len(g1) * len(g2)
    apack = np.empty((P, 2, 4), np.int8)
    for i1, p1 in enumerate(g1):
        for i2, p2 in enumerate(g2):
            p = i1 * len(g2) + i2
            for b in (0, 1):
                for s in range(4):
                    apack[p, b, s] = ((p1[b] >> s) & 1) + 2 * ((p2[b] >> s) & 1)
    found = []
    for lo in range(0, NE, NE_CHUNK):
        hi = min(lo + NE_CHUNK, NE)
        C = np.zeros((hi - lo, P), np.int16)
        for b in (0, 1):
            for s in range(4):
                M = D3V[idxE[lo:hi, b, s], :]
                C += M[:, apack[:, b, s]]
        for ke, kp in np.argwhere(C <= collect_max):
            found.append((int(C[ke, kp]), lo + int(ke), int(kp)))
    return found, (cos0, cos3, cos4, g1, g2, (I0, I3, I4))


def aug4(v):
    a = 0
    for x in v:
        a ^= x
    return a


NONZ = (1, 2, 3)
print("\n=== H6/H7: combo-family and kill-localization probes ===")
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C[0] @ zrep) % 2
    offs = comp_offsets(w0)
    found, (cos0, cos3, cos4, g1, g2, (I0, I3, I4)) = vfloor_combos(offs)
    c1 = xor4(offs[1][1], ring_mul4(rho1, offs[1][0]))
    c2 = xor4(offs[2][0], ring_mul4(rho2, offs[2][1]))
    sigs_full = set()
    sigs_masks = set()
    minw_hist = {}
    deficit_hist = {}
    crosstab = {}
    for cost, e, p in found:
        v0p = cos0[I0[e]]
        g3p = cos3[I3[e]]
        g4p = cos4[I4[e]]
        m1 = g1[p // len(g2)]
        m2 = g2[p % len(g2)]
        sig = (mask_of(v0p[0]), m1, m2,
               (mask_of(g3p[0]), mask_of(g3p[1])),
               (mask_of(g4p[0]), mask_of(g4p[1])))
        sigs_full.add(sig)
        sigs_masks.add((m1, m2))
        cand1 = []
        for vals in product(*[(NONZ if (m1[0] >> s) & 1 else (0,))
                              for s in range(4)]):
            vR = xor4(c1, ring_mul4(rho1, vals))
            if mask_of(vR) == m1[1]:
                cand1.append((vals, vR))
        cand2 = []
        for vals in product(*[(NONZ if (m2[1] >> s) & 1 else (0,))
                              for s in range(4)]):
            vL = xor4(c2, ring_mul4(rho2, vals))
            if mask_of(vL) == m2[0]:
                cand2.append((vL, vals))
        if not cand1 or not cand2:
            minw_hist["empty"] = minw_hist.get("empty", 0) + 1
            continue
        best_w, best_def = 10 ** 9, None
        for v1L, v1R in cand1:
            for v2L, v2R in cand2:
                wt = 0
                defs = []
                for b, (V0, V1, V2, V3, V4) in enumerate(
                        ((v0p[0], v1L, v2L, g3p[0], g4p[0]),
                         (v0p[1], v1R, v2R, g3p[1], g4p[1]))):
                    for s in range(4):
                        ww = int(WT_OF_VAL[V0[s], V1[s], V2[s], V3[s], V4[s]])
                        a1 = 1 if V1[s] else 0
                        a2 = 1 if V2[s] else 0
                        dd = ww - int(D3V[V0[s] * 16 + V3[s] * 4 + V4[s],
                                          a1 + 2 * a2])
                        wt += ww
                        defs.append(dd)
                if wt < best_w:
                    best_w, best_def = wt, defs
        minw_hist[best_w] = minw_hist.get(best_w, 0) + 1
        crosstab.setdefault(cost, {}).setdefault(best_w, 0)
        crosstab[cost][best_w] += 1
        dpat = tuple(sorted((d for d in best_def if d), reverse=True))
        deficit_hist[dpat] = deficit_hist.get(dpat, 0) + 1
    print(f"\n  orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): "
          f"{len(found)} combos at cost <= 10; "
          f"aug(c1) = {aug4(c1)}, aug(c2) = {aug4(c2)} (the aug-locks)")
    print(f"    distinct (m1, m2) mask families: {len(sigs_masks)}; "
          f"with v0/g3/g4 support data: {len(sigs_full)}")
    for cost in sorted(crosstab):
        print(f"    cost {cost}: min completion weights "
              f"{dict(sorted(crosstab[cost].items()))}")
    top = sorted(deficit_hist.items(), key=lambda kv: -kv[1])[:6]
    print(f"    minimal-completion deficit patterns (top): "
          f"{[(list(k), v) for k, v in top]}")

# =========================================================================
print("\n=== H10: the confined-value floor (rho-confinement, no grammar) ===")
# V1R = c1 + rho1 V1L is confined to c1 + im rho1 (16 vectors) because
# rho1^2 = 0; same for V2L.  Take comps {0,3,4} and the confined sides
# value-exactly, relax the free sides v1L, v2R per slot.  The cost then
# decomposes per block:  L-cost uses min over v1 (table M1), R-cost min
# over v2 (table M2), with V2L / V1R ranging over their 16-element sets.
M1T = WT_OF_VAL.min(axis=1)            # [v0, v2, v3, v4]: v1 relaxed
M2T = WT_OF_VAL.min(axis=2)            # [v0, v1, v3, v4]: v2 relaxed
IM_R1 = sorted({ring_mul4(rho1, t) for t in ALL_F4})
IM_R2 = sorted({ring_mul4(rho2, t) for t in ALL_F4})
print(f"  |im rho1| = {len(IM_R1)}, |im rho2| = {len(IM_R2)} (claim 16, 16)")
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C[0] @ zrep) % 2
    offs = comp_offsets(w0)
    cos0 = coset_pairs(offs, 0)
    cos3 = coset_pairs(offs, 3)
    cos4 = coset_pairs(offs, 4)
    c1 = xor4(offs[1][1], ring_mul4(rho1, offs[1][0]))
    c2 = xor4(offs[2][0], ring_mul4(rho2, offs[2][1]))
    V1R_SET = [xor4(c1, u) for u in IM_R1]
    V2L_SET = [xor4(c2, u) for u in IM_R2]
    best = 10 ** 9
    for g0 in cos0:
        for g3 in cos3:
            for g4 in cos4:
                lc = min(sum(int(M1T[g0[0][s], v2l[s], g3[0][s], g4[0][s]])
                             for s in range(4)) for v2l in V2L_SET)
                rc = min(sum(int(M2T[g0[1][s], v1r[s], g3[1][s], g4[1][s]])
                             for s in range(4)) for v1r in V1R_SET)
                best = min(best, lc + rc)
    print(f"  orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): "
          f"confined floor = {best}"
          + ("  -> closes (M-im) for this orbit outright" if best >= 12
             else "  -> residue: kill weight exactly 10"))

print("\nDone.")

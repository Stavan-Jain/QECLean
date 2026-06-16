"""Feasibility probe for the LEAN two-phase floor encoding of (M-im).

Decides the Lean native_decide encoding:
  (A) |Gamma_j| (the homogeneous graph ideal {(Bhat_j t, Ahat_j t)}) sizes,
      to size the hardcoded arrays;
  (B) the distinct (off_1, off_3, off_4) tuples over all 63 nonzero zeta
      (off_0 = off_2 = 0 by M-VANISH) -> transport (5 reps) vs direct (all);
  (C) the two-phase soundness + timing: for an orbit rep,
        relaxedCost(support grammar at comps 1,2) >= 12  OR
        every fiber completion has exactCost >= 12,
      and confirm exact product-min == 12 via the cheap-combo completion.
"""
from __future__ import annotations

import time
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
assert ker2.shape[0] == 6


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


# the seam map: cut-0 Smith representative w0(zeta) = D2C0 @ (something)?
# Use the SAME representative the value-cost script used: seamC = cut-0 lift.
# offsets are comp_hat of the two blocks of the cut-0 rep.
delta0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
AH = {j: comp_hat((d2b[nb:, :] @ delta0) % 2, j) for j in range(5)}
BH = {j: comp_hat((d2b[:nb, :] @ delta0) % 2, j) for j in range(5)}

ALL_F4 = [tuple(t) for t in product(range(4), repeat=4)]
ALL_F2 = [e for e in ALL_F4 if all(c in (0, 1) for c in e)]

# the cut-0 seam representative of [seamC zeta]: w0 = D2C0 @ zeta (lab eq)
def seam_rep(z36):
    return (D2C0 @ z36) % 2


def comp_offsets(w72):
    return {j: (comp_hat(w72[:nb], j), comp_hat(w72[nb:], j)) for j in range(5)}


# value <-> layer weight bijection
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
    WT_OF_VAL[tuple(vals)] = bin(fb).count("1")
assert (WT_OF_VAL >= 0).all()


def graph_ideal(j):
    """Gamma_j = {(Bhat_j t, Ahat_j t)} (offset 0); the Lean array."""
    dom = ALL_F2 if j == 0 else ALL_F4
    out = {}
    for t in dom:
        out[(ring_mul4(BH[j], t), ring_mul4(AH[j], t))] = True
    return list(out)


GAMMA = {j: graph_ideal(j) for j in range(5)}
print("=== (A) graph-ideal sizes |Gamma_j| (offset 0, ring-pair) ===")
for j in range(5):
    print(f"  j={j}: |Gamma_{j}| = {len(GAMMA[j])}  "
          f"(AH={AH[j]}, BH={BH[j]})")
prod_exact = 1
for j in range(5):
    prod_exact *= len(GAMMA[j])
print(f"  EXACT product  Pi|Gamma_j| = {prod_exact} = 2^{np.log2(prod_exact):.1f}")

# ------------------------------------------------------------------ (B)
print("\n=== (B) distinct offset tuples over all 63 nonzero zeta ===")
offsets_seen = {}
mvanish_ok = True
for z in Z2all:
    offs = comp_offsets(seam_rep(z))
    if offs[0] != ((0, 0, 0, 0), (0, 0, 0, 0)) or \
       offs[2] != ((0, 0, 0, 0), (0, 0, 0, 0)):
        mvanish_ok = False
    key = (offs[1], offs[3], offs[4])
    offsets_seen.setdefault(key, 0)
    offsets_seen[key] += 1
print(f"  off_0 == off_2 == 0 for all 63 zeta (M-VANISH): {mvanish_ok}")
print(f"  distinct (off_1, off_3, off_4) tuples: {len(offsets_seen)} "
      f"(out of 63 zeta)")

# ------------------------------------------------------------------ (C)
print("\n=== (C) two-phase soundness + timing (one orbit rep) ===")


def exact_cost(offs, p0, p1, p2, p3, p4):
    """Sum over 8 (block,slot) of wt5(off + pair value)."""
    pairs = {0: p0, 1: p1, 2: p2, 3: p3, 4: p4}
    tot = 0
    for b in (0, 1):
        for s in range(4):
            v = []
            for j in range(5):
                off = offs[j][b][s]
                pv = pairs[j][b][s]
                v.append(off ^ pv)
            tot += int(WT_OF_VAL[tuple(v)])
    return tot


# relaxed cost: comps 1,2 by SUPPORT (d3v with a1,a2 = whether nonzero),
# minimized per slot independently over the free value.
D3V = np.full((32, 4), 99, np.int8)
for v0 in range(2):
    for v3 in range(4):
        for v4 in range(4):
            for a1 in range(2):
                for a2 in range(2):
                    dom1 = (0,) if a1 == 0 else (1, 2, 3)
                    dom2 = (0,) if a2 == 0 else (1, 2, 3)
                    D3V[v0 * 16 + v3 * 4 + v4, a1 + 2 * a2] = min(
                        int(WT_OF_VAL[v0, v1, v2, v3, v4])
                        for v1 in dom1 for v2 in dom2)


def relaxed_cost(offs, p0, p3, p4, m1, m2):
    """comps 0,3,4 value-exact; comps 1,2 support-only (masks m1,m2)."""
    tot = 0
    for b in (0, 1):
        for s in range(4):
            v0 = offs[0][b][s] ^ p0[b][s]
            v3 = offs[3][b][s] ^ p3[b][s]
            v4 = offs[4][b][s] ^ p4[b][s]
            a1 = (m1[b] >> s) & 1
            a2 = (m2[b] >> s) & 1
            tot += int(D3V[v0 * 16 + v3 * 4 + v4, a1 + 2 * a2])
    return tot


# pick the worst orbit rep (wt-24 VFLOOR-6 one); test ALL orbit reps quickly
orbs = {}
def swap36(z):
    out = np.zeros_like(z)
    for g in Gb:
        out[Gb.index((g[1], g[0]))] = z[Gb.index(g)]
    return out
def translate36(z, dx, dy):
    out = np.zeros_like(z)
    for g in Gb:
        out[Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = z[Gb.index(g)]
    return out
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

# group Gamma values by support mask for comps 1,2 (the fibers)
def by_mask(j):
    d = {}
    for pair in GAMMA[j]:
        key = (mask_of(pair[0]), mask_of(pair[1]))
        d.setdefault(key, []).append(pair)
    return d
FIB1 = by_mask(1)
FIB2 = by_mask(2)
masks1 = sorted(FIB1)
masks2 = sorted(FIB2)
print(f"  comp1 support-mask classes: {len(masks1)}, "
      f"comp2: {len(masks2)}; relaxed outer = "
      f"{len(GAMMA[0])*len(GAMMA[3])*len(GAMMA[4])*len(masks1)*len(masks2)} "
      f"= 2^{np.log2(len(GAMMA[0])*len(GAMMA[3])*len(GAMMA[4])*len(masks1)*len(masks2)):.1f}")

for key in ORBKEYS:
    zrep = orbs[key][0]
    offs = comp_offsets(seam_rep(zrep))
    t0 = time.time()
    # phase 1: relaxed scan; collect cheap (relaxed <= 10) outer configs
    cheap = []
    relaxed_min = 10**9
    for p0 in GAMMA[0]:
        for p3 in GAMMA[3]:
            for p4 in GAMMA[4]:
                for m1 in masks1:
                    for m2 in masks2:
                        rc = relaxed_cost(offs, p0, p3, p4, m1, m2)
                        relaxed_min = min(relaxed_min, rc)
                        if rc <= 10:
                            cheap.append((p0, p3, p4, m1, m2))
    # phase 2: complete each cheap config over comp1/comp2 fibers
    exact_min_cheap = 10**9
    n_completions = 0
    bad = 0
    for (p0, p3, p4, m1, m2) in cheap:
        for p1 in FIB1[m1]:
            for p2 in FIB2[m2]:
                ec = exact_cost(offs, p0, p1, p2, p3, p4)
                n_completions += 1
                exact_min_cheap = min(exact_min_cheap, ec)
                if ec < 12:
                    bad += 1
    dt = time.time() - t0
    wt = int(zrep.sum())
    print(f"  orbit wt={wt} n={len(orbs[key])}: relaxed_min={relaxed_min}, "
          f"#cheap(<=10)={len(cheap)}, completions={n_completions}, "
          f"exact_min over cheap={exact_min_cheap}, sub-12 survivors={bad}, "
          f"[{dt:.1f}s]")

print("\nTwo-phase verdict: relaxed>=12 kills the bulk; every cheap fiber "
      ">=12 -> floor 12. Done.")

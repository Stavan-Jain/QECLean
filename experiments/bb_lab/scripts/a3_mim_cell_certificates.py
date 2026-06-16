"""A3 / Track 1.1 Entry 24 — O1 cell certificates: the engine evaluates every
spine cell exactly; block >= 6 closes the wt-24 orbits.

The Entry-23 engines, assembled into a per-cell evaluator that uses ONLY
the hand lemmas — never the raw M-tables:

  per slot (v0 free, unlinked form):   n alive in (conf, 3, 4):
      n = 0 -> 0;  n = 1 -> 3;  n = 2 -> 2;
      n = 3 -> 1 if the slot is in the chosen cheap level set else 3;
  cheap level sets:  the confined comp contributes one free scale, so
      the simultaneously-cheap 3-alive slots are a level set of
      h_L(s) = v3(s) v4(s) (m(s)+m(z2))^{-2}   (co-point mode, level p^2)
      h_L'(s) = v3(s) v4(s)                    (full-const mode, level q^2)
      h_R(s) = v4(s) v3(s)^{-1} (m'(s)+m'(z1))^{-1}  (level p)
      h_R'(s) = v4(s) v3(s)^{-1}               (level q);
  supports and values: comp 3: v3 = k3 + d3 alive off the level set of
      k3 at d3 (d3 in F4 free); comp 4: same with k4, d4; confined comp:
      dead / co-point z (values p(m + m(z))) / full-constant.

Linked form (shared V0 and gamma): per slot v0 is FIXED by V0 and
      d4 is driven by gamma (d4L = w*gamma + const_L, d4R = gamma +
      const_R); slot costs: v0=0: (0, 4, 2, 2/4-cheap); v0=1:
      (3, 3, 3, 1/3-cheap).

Sections:
  E1  engine == truth for all 5 orbits x 16 cells x 2 blocks (unlinked
      block minima; truth = brute force over the raw M-tables);
  E2  the wt-24 closure: every block >= 6 in every cell, so every
      spine cell has m >= 12: (M-im) holds for the wt-24 cosets at the
      level of the proven engine lemmas + these 2x16-cell tables;
  E3  engine == truth for the LINKED cell values m(a3, a4) (all orbits);
      the floor-10 cells of wt-16/18a/18b confirmed engine-exactly;
  E4  certificate dump for the write-up: per wt-24 cell, the minimal
      alignments (mode, d3, d4, n-profile, h-level multiplicities) —
      the rows a human checks against the engine lemmas.

Discovery/validation only; the load-bearing argument is the engine
lemmas (proven in Entry 23) + the per-cell tables this script verifies.
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
F4_INV = {1: 1, 2: 3, 3: 2}
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


XYr = (1, 1, 1, 1)
rho1 = ring_mul4(AH[1], inv4(BH[1]))
rho2 = ring_mul4(BH[2], inv4(AH[2]))


def in_xy_basis(v):
    d = v[3]
    c = v[2] ^ d
    b = v[1] ^ d
    a = v[0] ^ b ^ c ^ d
    return (a, b, c, d)


def kill_vec(v):
    a, al, be, _ = in_xy_basis(v)
    return (a ^ al ^ be, al, be, 0)


M_L = kill_vec(rho2)          # confined-comp kill vector, L block (comp 2)
M_R = kill_vec(rho1)          # R block (comp 1)

# truth tables (for verification only)
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
    ORB_DATA[key] = comp_offsets(w0)


def cell_bases(key, a3, a4, block):
    """Kill vectors of the comp-3/4 bases, plus the XY-coefficient of the
    comp-4 base (needed to tie the two blocks' shifts through gamma)."""
    offs = ORB_DATA[key]
    if block == 0:
        b3 = xor4(offs[3][0], smul(a3, BH[3]))
        b4 = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
    else:
        b3 = xor4(offs[3][1], smul(a3, AH[3]))
        b4 = xor4(offs[4][1], smul(a4, AH[4]))
    return kill_vec(b3), kill_vec(b4), in_xy_basis(b4)[3]


def engine_block(key, a3, a4, block, v0fix=None, g4fix=None, detail=False):
    """The engine evaluation of one block at one cell.

    v0fix: fixed V0 (tuple of 4 bits) or None (per-slot free min);
    g4fix: fixed d4 (the comp-4 TOTAL kill-shift) or None (free)."""
    k3, k4, _ = cell_bases(key, a3, a4, block)
    m = M_L if block == 0 else M_R
    best, arg = 10 ** 9, None
    modes = [("dead", None)] + [("co", z) for z in range(4)] + [("full", None)]
    for d3 in range(4):
        alive3 = [k3[s] != d3 for s in range(4)]
        v3 = [k3[s] ^ d3 for s in range(4)]
        for d4 in ([g4fix] if g4fix is not None else range(4)):
            alive4 = [k4[s] != d4 for s in range(4)]
            v4 = [k4[s] ^ d4 for s in range(4)]
            for mode, z in modes:
                if mode == "dead":
                    aliveC = [False] * 4
                elif mode == "co":
                    aliveC = [s != z for s in range(4)]
                else:
                    aliveC = [True] * 4
                A3 = [s for s in range(4)
                      if aliveC[s] and alive3[s] and alive4[s]]
                hs = {}
                for s in A3:
                    prod34 = f4m(v3[s], v4[s])
                    if block == 0:
                        if mode == "co":
                            d = m[s] ^ m[z]
                            h = f4m(prod34, F4_INV[f4m(d, d)])
                        else:
                            h = prod34
                    else:
                        r = f4m(v4[s], F4_INV[v3[s]])
                        if mode == "co":
                            h = f4m(r, F4_INV[m[s] ^ m[z]])
                        else:
                            h = r
                    hs[s] = h
                # cost over cheap-level choices
                for lev in set(hs.values()) | {None}:
                    tot = 0
                    for s in range(4):
                        n = aliveC[s] + alive3[s] + alive4[s]
                        cheap = (s in hs and lev is not None
                                 and hs[s] == lev)
                        if v0fix is None:
                            tot += (0, 3, 2, 1 if cheap else 3)[n]
                        else:
                            if v0fix[s]:
                                tot += (3, 3, 3, 1 if cheap else 3)[n]
                            else:
                                tot += (0, 4, 2, 2 if cheap else 4)[n]
                    if tot < best:
                        best = tot
                        arg = (mode, z, d3, d4,
                               tuple(aliveC[s] + alive3[s] + alive4[s]
                                     for s in range(4)),
                               dict(hs), lev)
    return (best, arg) if detail else best


def true_block(key, a3, a4, block):
    offs = ORB_DATA[key]
    Mtab = M1 if block == 0 else M2
    rho = rho2 if block == 0 else rho1
    if block == 0:
        b3 = xor4(offs[3][0], smul(a3, BH[3]))
        b4core = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
    else:
        b3 = xor4(offs[3][1], smul(a3, AH[3]))
        b4core = xor4(offs[4][1], smul(a4, AH[4]))
    best = 10 ** 9
    for V0 in ALL_F2:
        for gs in range(4):
            V4 = xor4(b4core, smul(gs, XYr))
            for sh in range(4):
                V3 = xor4(b3, smul(sh, XYr))
                for p in range(4):
                    for q in range(4):
                        Vc = xor4(smul(p, rho), smul(q, XYr))
                        tot = sum(int(Mtab[V0[s], Vc[s], V3[s], V4[s]])
                                  for s in range(4))
                        best = min(best, tot)
    return best


# =========================================================================
print("=== E1: engine == truth, unlinked block minima (5 x 16 x 2) ===")
ok_e1 = True
for key in ORBKEYS:
    for a3 in range(4):
        for a4 in range(4):
            for blk in (0, 1):
                e = engine_block(key, a3, a4, blk)
                t = true_block(key, a3, a4, blk)
                if e != t:
                    ok_e1 = False
                    print(f"  MISMATCH {ONAME[key]} cell ({a3},{a4}) "
                          f"block {blk}: engine {e} vs true {t}")
print(f"  engine == truth on all 160 block cells: {ok_e1}")

print("\n=== E2: the wt-24 closure ===")
for key in ORBKEYS[3:]:
    mins = [engine_block(key, a3, a4, blk)
            for a3 in range(4) for a4 in range(4) for blk in (0, 1)]
    print(f"  {ONAME[key]}: min block value over all cells = {min(mins)} "
          f"(>= 6 closes (M-im) here: {min(mins) >= 6})")

# =========================================================================
print("\n=== E3: engine == truth for the linked cell values m(a3, a4) ===")


def engine_cell_exact(key, a3, a4):
    """The linked cell value via the engine: V0 and gamma shared; the
    comp-4 kill-shifts of the two blocks are d0L + w*gamma and
    d0R + gamma (d0 = the XY-coefficient of each block's comp-4 base,
    which the kill vector drops)."""
    _, _, d0L = cell_bases(key, a3, a4, 0)
    _, _, d0R = cell_bases(key, a3, a4, 1)
    best = 10 ** 9
    for gamma in range(4):
        d4L, d4R = d0L ^ f4m(W, gamma), d0R ^ gamma
        for V0 in ALL_F2:
            l = engine_block(key, a3, a4, 0, v0fix=V0, g4fix=d4L)
            r = engine_block(key, a3, a4, 1, v0fix=V0, g4fix=d4R)
            best = min(best, l + r)
    return best


def true_cell(key, a3, a4):
    offs = ORB_DATA[key]
    b3L = xor4(offs[3][0], smul(a3, BH[3]))
    b3R = xor4(offs[3][1], smul(a3, AH[3]))
    b4L = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
    b4R = xor4(offs[4][1], smul(a4, AH[4]))
    best = 10 ** 9
    for gamma in range(4):
        V4L = xor4(b4L, smul(f4m(W, gamma), XYr))
        V4R = xor4(b4R, smul(gamma, XYr))
        for V0 in ALL_F2:
            lmin = 10 ** 9
            for be in range(4):
                V3 = xor4(b3L, smul(be, XYr))
                for p in range(4):
                    for q in range(4):
                        Vc = xor4(smul(p, rho2), smul(q, XYr))
                        tot = sum(int(M1[V0[s], Vc[s], V3[s], V4L[s]])
                                  for s in range(4))
                        lmin = min(lmin, tot)
            rmin = 10 ** 9
            for al in range(4):
                V3 = xor4(b3R, smul(al, XYr))
                for p in range(4):
                    for q in range(4):
                        Vc = xor4(smul(p, rho1), smul(q, XYr))
                        tot = sum(int(M2[V0[s], Vc[s], V3[s], V4R[s]])
                                  for s in range(4))
                        rmin = min(rmin, tot)
            best = min(best, lmin + rmin)
    return best


ok_e3 = True
for key in ORBKEYS:
    grid_e = np.zeros((4, 4), int)
    grid_t = np.zeros((4, 4), int)
    for a3 in range(4):
        for a4 in range(4):
            grid_e[a3, a4] = engine_cell_exact(key, a3, a4)
            grid_t[a3, a4] = true_cell(key, a3, a4)
    same = (grid_e == grid_t).all()
    ok_e3 &= bool(same)
    print(f"  {ONAME[key]}: engine grid == true grid: {same}; "
          f"floor {grid_e.min()}")
print(f"  engine == truth on all 80 linked cells: {ok_e3}")

# =========================================================================
print("\n=== E4: certificate exemplars (wt-24 cells, block level) ===")
for key in ORBKEYS[3:]:
    print(f"\n  {ONAME[key]}:")
    for a3 in range(4):
        for a4 in range(4):
            for blk in (0, 1):
                v, arg = engine_block(key, a3, a4, blk, detail=True)
                if (a3, a4) in [(0, 0), (1, 1)]:        # exemplar cells
                    mode, z, d3, d4, nprof, hs, lev = arg
                    print(f"    cell ({a3},{a4}) blk {blk}: min {v} via "
                          f"mode {mode}{'' if z is None else z}, d3 {d3}, "
                          f"d4 {d4}, n-profile {nprof}, h {hs}, level {lev}")

print("\nDone.")

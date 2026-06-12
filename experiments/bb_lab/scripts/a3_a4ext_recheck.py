"""A3 Entry 28 — recheck of the A4 Part-II compressed tables (F/W/K).

Verifies every numerical claim and table of `notes/A4_writeup.md`
Part II (§§8–14, Appendix C) against independent recomputation:

  F1  the labelings m, m', m'^2 = w^2 m, kill(rho_i); bijectivity.
  F2  the confined comps are the affine lines {p m + c} / {p m' + c}.
  F3  the comp-4 tie V4L = w V4R + w4; the e_L/e_R/d_w table.
  F4  the per-orbit offset (kill-vector) table of §10.1.
  F5  the fibre-type tables driving §§11–12 (pair-ratio lemma output).
  F6  the hyperbolic quadruples: (m, m + w*theta) = H_{w^2}; no three
      collinear (the §10.4 instances).
  W1  S(a,b) == 6 for all (a,b) (v0-free standard form).
  W2  the four wt-24 block tables equal the S-reindexings of §10.5.
  W3  the §11 / C.1 bucket minima (exact, all >= 6).
  K1  per-cell linked floors: wt-24 cells all >= 12; wt-16/18 cells
      >= 10 with the floor-10 cells as listed; per-(V0,gamma) block
      minima sums all even and >= 10.
  K2  the C.2–C.4 locus tables (loci and split values, exact).
  K3  the 118 achievers (48/48/22; per-cell counts) and the rho-link
      kills: 116 fail both links, 2 fail exactly one, 0 survive; the
      §13 worked-kill convolution.
  K4  the achiever-structure lemma instance: the achiever set equals
      the union over sum-10 loci of Argmin_L x Argmin_R.

Confirmation only; the load-bearing argument is the A4 Part-II prose.
Run: uv run python scripts/a3_a4ext_recheck.py   (from experiments/bb_lab)
"""
from __future__ import annotations

from itertools import product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2

FAILURES = []


def check(name, ok):
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
    if not ok:
        FAILURES.append(name)


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
# canonical names: wt-16, wt-18a (n=12), wt-18b (n=36), wt-24a, wt-24b
ONAME = dict(zip(ORBKEYS, ["wt-16", "wt-18a", "wt-18b", "wt-24a", "wt-24b"]))

F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        F4_MUL[a, b_] = ((a0 & b0) ^ (a1 & b1)) | \
            ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))
ORBITS5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, 2, 3]
W = 2          # omega
W2 = 3         # omega^2


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


def in_xy_basis(v):
    d = v[3]
    c = v[2] ^ d
    b = v[1] ^ d
    a = v[0] ^ b ^ c ^ d
    return (a, b, c, d)


def kill_vec(v):
    a, al, be, _ = in_xy_basis(v)
    return (a ^ al ^ be, al, be, 0)


# =========================================================================
print("=== F1: labelings ===")
m = kill_vec(BH[3])
mp = kill_vec(AH[3])
mp2 = kill_vec(AH[4])
check("m = kill(Bhat) = (w2,w,1,0)", m == (3, 2, 1, 0))
check("m' = m o (x<->y)", mp == (m[0], m[2], m[1], m[3]))
check("kill(Ahat4) = m'^2 = w^2 m",
      mp2 == tuple(f4m(x, x) for x in mp) and mp2 == smul(W2, m))
check("m^2 = w^2 m'", tuple(f4m(x, x) for x in m) == smul(W2, mp))
check("kill(rho2) = m, kill(rho1) = m'",
      kill_vec(rho2) == m and kill_vec(rho1) == mp)
check("m, m' bijections", sorted(m) == [0, 1, 2, 3] and
      sorted(mp) == [0, 1, 2, 3])

print("=== F2: confined lines ===")
check("im rho2 = {p m + c}",
      set(IMR2) == {tuple(f4m(p, m[s]) ^ c for s in range(4))
                    for p in range(4) for c in range(4)})
check("im rho1 = {p m' + c}",
      set(IMR1) == {tuple(f4m(p, mp[s]) ^ c for s in range(4))
                    for p in range(4) for c in range(4)})

print("=== F3: comp-4 tie and the e/d_w table ===")
CLAIM_E = {"wt-16": (W, W), "wt-18a": (W2, W2), "wt-18b": (1, 1),
           "wt-24a": (W2, 1), "wt-24b": (1, W2)}
for key in ORBKEYS:
    offs = ORB_DATA[key]
    w4 = xor4(offs[4][0], smul(W, offs[4][1]))
    ok = all(xor4(smul(W, xor4(offs[4][1], ring_mul4(AH[4], t))),
                  xor4(offs[4][0], ring_mul4(BH[4], t))) == w4
             for t in ALL_F4)
    eL = in_xy_basis(offs[4][0])[3]
    eR = in_xy_basis(offs[4][1])[3]
    dw = in_xy_basis(w4)[3]
    name = ONAME[key]
    check(f"{name}: tie V4L = w V4R + w4 on all 256 cosets", ok)
    check(f"{name}: (e_L, e_R) as in §10.1 and e_L = w e_R + d_w",
          (eL, eR) == CLAIM_E[name] and eL == f4m(W, eR) ^ dw)

print("=== F4: the §10.1 offset table ===")
TH = (1, 0, 1, 0)
CLAIM_K = {
    "wt-16":  (smul(W, TH), TH, smul(W, TH), TH),
    "wt-18a": (m, mp, (0, 2, 3, 0), (3, 3, 3, 0)),
    "wt-18b": ((1, 2, 3, 0), smul(W2, m), (2, 2, 1, 0), (2, 3, 2, 0)),
    "wt-24a": ((0, 0, 0, 0), (0, 0, 0, 0), smul(W, TH), TH),
    "wt-24b": (smul(W, TH), TH, (0, 0, 0, 0), (0, 0, 0, 0)),
}
for key in ORBKEYS:
    offs = ORB_DATA[key]
    got = (kill_vec(offs[3][0]), kill_vec(offs[3][1]),
           kill_vec(offs[4][0]), kill_vec(offs[4][1]))
    check(f"{ONAME[key]}: (kappa3L, kappa3R, kappa4L, kappa4R)",
          got == CLAIM_K[ONAME[key]])
    # spine-affinity of the cell kill vectors, with k4 multipliers a4*m
    # on L (the w-twist absorbed) and w^2 a4*m on R
    ok = all(
        kill_vec(xor4(offs[3][0], smul(a, BH[3]))) ==
        xor4(CLAIM_K[ONAME[key]][0], smul(a, m)) and
        kill_vec(xor4(offs[3][1], smul(a, AH[3]))) ==
        xor4(CLAIM_K[ONAME[key]][1], smul(a, mp)) and
        kill_vec(xor4(offs[4][0], smul(W, smul(a, AH[4])))) ==
        xor4(CLAIM_K[ONAME[key]][2], smul(a, m)) and
        kill_vec(xor4(offs[4][1], smul(a, AH[4]))) ==
        xor4(CLAIM_K[ONAME[key]][3], smul(f4m(W2, a), m))
        for a in range(4))
    check(f"{ONAME[key]}: cell directions affine in the spine", ok)

print("=== F5: fibre types (pair-ratio lemma output) ===")


def fibre_type(k):
    from collections import Counter
    return "+".join(str(s) for s in
                    sorted(Counter(k).values(), reverse=True))


# S-form comp-4 trichotomy of §10.3
got = [fibre_type(xor4(smul(b, m), smul(W, TH))) for b in range(4)]
check("S-form k4 = b m + w theta types: 2+2 / 1+1+1+1 / 2+2 / 2+2",
      got == ["2+2", "1+1+1+1", "2+2", "2+2"])
pair_sets = {}
for b in (0, 2, 3):
    k = xor4(smul(b, m), smul(W, TH))
    fib = {}
    for s in range(4):
        fib.setdefault(k[s], []).append(s)
    pair_sets[b] = sorted(tuple(v) for v in fib.values())
check("pairings: b=0 {e,y|x,xy}, b=w {e,x|y,xy}, b=w2 {e,xy|x,y}",
      pair_sets[0] == [(0, 2), (1, 3)] and
      pair_sets[2] == [(0, 1), (2, 3)] and
      pair_sets[3] == [(0, 3), (1, 2)])

print("=== F6: hyperbolic quadruples ===")


def no3collinear(pts):
    n = len(pts)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                (x1, y1), (x2, y2), (x3, y3) = pts[i], pts[j], pts[k]
                if f4m(y1 ^ y2, x1 ^ x3) == f4m(y1 ^ y3, x1 ^ x2):
                    return False
    return True


k4_1 = xor4(m, smul(W, TH))
pts = [(m[s], k4_1[s]) for s in range(4)]
check("(m, m + w theta) products = {w2, w2, w2, 0} (H_{w^2})",
      sorted(f4m(u, v) for u, v in pts) == [0, 3, 3, 3])
check("no three of (m, m + w theta) collinear", no3collinear(pts))

# =========================================================================
print("=== W1: the standard form S(a,b) ===")


def s_block_min(a, b):
    best = 10 ** 9
    for p in range(4):
        for c2 in range(4):
            v2 = tuple(f4m(p, m[s]) ^ c2 for s in range(4))
            for c3 in range(4):
                v3 = tuple(f4m(a, m[s]) ^ c3 for s in range(4))
                for c4 in range(4):
                    v4 = tuple(f4m(b, m[s]) ^ f4m(W, TH[s]) ^ c4
                               for s in range(4))
                    tot = sum(min(int(M1[0, v2[s], v3[s], v4[s]]),
                                  int(M1[1, v2[s], v3[s], v4[s]]))
                              for s in range(4))
                    best = min(best, tot)
    return best


grid_S = {(a, b): s_block_min(a, b) for a in range(4) for b in range(4)}
check("S(a,b) = 6 for all 16 (a,b)", all(v == 6 for v in grid_S.values()))

print("=== W2: the wt-24 block tables are S-reindexings ===")
FROB = [0, 1, 3, 2]


def true_block_min(key, blk, a3, a4):
    offs = ORB_DATA[key]
    Mtab = M1 if blk == 0 else M2
    rho = rho2 if blk == 0 else rho1
    if blk == 0:
        b3 = xor4(offs[3][0], smul(a3, BH[3]))
        b4c = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
    else:
        b3 = xor4(offs[3][1], smul(a3, AH[3]))
        b4c = xor4(offs[4][1], smul(a4, AH[4]))
    best = 10 ** 9
    for V0 in ALL_F2:
        for gs in range(4):
            V4 = xor4(b4c, smul(gs, XYr))
            for sh in range(4):
                V3 = xor4(b3, smul(sh, XYr))
                for pp in range(4):
                    for qq in range(4):
                        Vc = xor4(smul(pp, rho), smul(qq, XYr))
                        tot = sum(int(Mtab[V0[s], Vc[s], V3[s], V4[s]])
                                  for s in range(4))
                        best = min(best, tot)
    return best


k24a = next(k for k in ORBKEYS if ONAME[k] == "wt-24a")
k24b = next(k for k in ORBKEYS if ONAME[k] == "wt-24b")
maps = [("L(24a) = S(a3,a4)", k24a, 0, lambda a3, a4: (a3, a4)),
        ("R(24a) = S(a3,a4^2)", k24a, 1, lambda a3, a4: (a3, FROB[a4])),
        ("L(24b) = S(a4,a3)", k24b, 0, lambda a3, a4: (a4, a3)),
        ("R(24b) = S(a4^2,a3)", k24b, 1, lambda a3, a4: (FROB[a4], a3))]
for lab, key, blk, f in maps:
    ok = all(true_block_min(key, blk, a3, a4) == grid_S[f(a3, a4)]
             for a3 in range(4) for a4 in range(4))
    check(lab, ok)

print("=== W3: the C.1 bucket minima ===")
CLAIM_BUCKETS = {
    "A1|2": 6, "A1|3": 9, "A1|4": 12, "A2|2": 7, "A2|3": 6, "A2|4": 9,
    "A3|2": 10, "A3|3": 9, "A3|4": 8, "A4|2": 10, "A4|3": 9, "A4|4": 8,
    "A5|2": 7, "A5|3": 6, "A5|4": 7, "A6|2": 6, "A6|3": 9, "A6|4": 8,
    "B1|b=1": 6, "B1|2": 7, "B1|4": 9, "B2|b=1": 6, "B2|2": 7, "B2|4": 7,
    "B3|z=,2": 6, "B3|z=,4": 8, "B3|z!,2": 8, "B3|z!,4": 6,
    "B4|zzz": 7, "B4|z23": 7, "B4|z24": 9, "B4|z34": 9, "B4|dist": 7,
}


def bucket_of(a, b, p, c2, c3, c4):
    v3 = tuple(f4m(a, m[s]) ^ c3 for s in range(4))
    v4 = tuple(f4m(b, m[s]) ^ f4m(W, TH[s]) ^ c4 for s in range(4))
    S4 = sum(1 for s in range(4) if v4[s])
    z2 = next((s for s in range(4) if f4m(p, m[s]) == c2), None) \
        if p else None
    z3 = next((s for s in range(4) if v3[s] == 0), None) if a else None
    z4 = next((s for s in range(4) if v4[s] == 0), None) if S4 == 3 else None
    cm = "dead" if (p == 0 and c2 == 0) else ("full" if p == 0 else "co")
    if a == 0:
        comp3 = "dead" if c3 == 0 else "full"
        row = {("dead", "dead"): "A1", ("dead", "co"): "A2",
               ("dead", "full"): "A3", ("full", "dead"): "A4",
               ("full", "co"): "A5", ("full", "full"): "A6"}[(comp3, cm)]
        return f"{row}|{S4}"
    if cm == "dead":
        return "B1|b=1" if b == 1 else f"B1|{S4}"
    if cm == "full":
        return "B2|b=1" if b == 1 else f"B2|{S4}"
    if b != 1:
        return f"B3|{'z=' if z2 == z3 else 'z!'},{S4}"
    if z2 == z3 == z4:
        return "B4|zzz"
    if z2 == z3:
        return "B4|z23"
    if z2 == z4:
        return "B4|z24"
    if z3 == z4:
        return "B4|z34"
    return "B4|dist"


got_buckets = {}
for a in range(4):
    for b in range(4):
        for p in range(4):
            for c2 in range(4):
                if p == 0 and c2 not in (0, 1):
                    pass  # all c2 values are distinct constants; keep all
                v2 = tuple(f4m(p, m[s]) ^ c2 for s in range(4))
                for c3 in range(4):
                    v3 = tuple(f4m(a, m[s]) ^ c3 for s in range(4))
                    for c4 in range(4):
                        v4 = tuple(f4m(b, m[s]) ^ f4m(W, TH[s]) ^ c4
                                   for s in range(4))
                        lab = bucket_of(a, b, p, c2, c3, c4)
                        tot = sum(min(int(M1[0, v2[s], v3[s], v4[s]]),
                                      int(M1[1, v2[s], v3[s], v4[s]]))
                                  for s in range(4))
                        if lab not in got_buckets or tot < got_buckets[lab]:
                            got_buckets[lab] = tot
check("bucket set matches C.1 (33 buckets)",
      set(got_buckets) == set(CLAIM_BUCKETS))
check("bucket minima match C.1 exactly",
      all(got_buckets.get(k) == v for k, v in CLAIM_BUCKETS.items()))
check("all buckets >= 6", all(v >= 6 for v in got_buckets.values()))

# =========================================================================
print("=== K1: per-cell linked floors ===")


def block_min_at(key, a3, a4, blk, V0, gamma):
    offs = ORB_DATA[key]
    if blk == 0:
        b3 = xor4(offs[3][0], smul(a3, BH[3]))
        b4 = xor4(xor4(offs[4][0], smul(W, smul(a4, AH[4]))),
                  smul(f4m(W, gamma), XYr))
        confs, Mtab = IMR2, M1
    else:
        b3 = xor4(offs[3][1], smul(a3, AH[3]))
        b4 = xor4(xor4(offs[4][1], smul(a4, AH[4])), smul(gamma, XYr))
        confs, Mtab = IMR1, M2
    best = 10 ** 9
    for d3 in range(4):
        V3 = xor4(b3, smul(d3, XYr))
        for conf in confs:
            tot = sum(int(Mtab[V0[s], conf[s], V3[s], b4[s]])
                      for s in range(4))
            best = min(best, tot)
    return best


CLAIM_FLOOR10 = {
    "wt-16": {(2, 1), (2, 3), (3, 1), (3, 3)},
    "wt-18a": {(a3, a4) for a3 in range(4) for a4 in range(4)}
    - {(1, 1), (1, 3)},
    "wt-18b": {(0, 1), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0),
               (2, 1), (2, 2), (3, 0), (3, 2), (3, 3)},
}
CELL_SUMS = {}
for key in ORBKEYS:
    name = ONAME[key]
    ok_even, ok_10, floors = True, True, {}
    for a3 in range(4):
        for a4 in range(4):
            cellmin = 10 ** 9
            sums = {}
            for gamma in range(4):
                for V0 in ALL_F2:
                    lm = block_min_at(key, a3, a4, 0, V0, gamma)
                    rm = block_min_at(key, a3, a4, 1, V0, gamma)
                    if (lm + rm) % 2:
                        ok_even = False
                    if lm + rm < 10:
                        ok_10 = False
                    sums[(V0, gamma)] = (lm, rm)
                    cellmin = min(cellmin, lm + rm)
            floors[(a3, a4)] = cellmin
            CELL_SUMS[(key, a3, a4)] = sums
    if name.startswith("wt-24"):
        check(f"{name}: all 16 cells >= 12",
              all(v >= 12 for v in floors.values()))
    else:
        check(f"{name}: per-(V0,gamma) sums even", ok_even)
        check(f"{name}: per-(V0,gamma) sums >= 10 (cost-8 kill)", ok_10)
        got10 = {c for c, v in floors.items() if v == 10}
        check(f"{name}: floor-10 cells as in §12", got10 ==
              CLAIM_FLOOR10[name] and
              all(v in (10, 12, 14) for v in floors.values()))

print("=== K2: the C.2–C.4 locus tables ===")
# loci written ((a3,a4), (lm,rm), V0-bitstring, gamma); spine/F4 coded
# 0,1,2,3 = 0,1,w,w2.
C2 = [  # wt-16 floor-10 cells
    ((2, 1), (5, 5), "0001", 0), ((2, 1), (5, 5), "0100", 1),
    ((2, 1), (5, 5), "0010", 2), ((2, 1), (5, 5), "1000", 3),
    ((2, 1), (6, 4), "1001", 0), ((2, 1), (6, 4), "0110", 1),
    ((2, 1), (6, 4), "0110", 2), ((2, 1), (6, 4), "1001", 3),
    ((2, 3), (5, 5), "0111", 0), ((2, 3), (5, 5), "1110", 0),
    ((2, 3), (5, 5), "1011", 3), ((2, 3), (5, 5), "1101", 3),
    ((2, 3), (6, 4), "1111", 0), ((2, 3), (6, 4), "0000", 1),
    ((2, 3), (6, 4), "0000", 2), ((2, 3), (6, 4), "1111", 3),
    ((3, 1), (4, 6), "1001", 0), ((3, 1), (4, 6), "0110", 1),
    ((3, 1), (4, 6), "0110", 2), ((3, 1), (4, 6), "1001", 3),
    ((3, 1), (5, 5), "1000", 0), ((3, 1), (5, 5), "0010", 1),
    ((3, 1), (5, 5), "0100", 2), ((3, 1), (5, 5), "0001", 3),
    ((3, 3), (4, 6), "1111", 0), ((3, 3), (4, 6), "0000", 1),
    ((3, 3), (4, 6), "0000", 2), ((3, 3), (4, 6), "1111", 3),
    ((3, 3), (5, 5), "1011", 0), ((3, 3), (5, 5), "1101", 0),
    ((3, 3), (5, 5), "0111", 3), ((3, 3), (5, 5), "1110", 3),
]
C3 = []  # wt-18a: classes expanded over a3 in {0, w, w2}
for a3 in (0, 2, 3):
    C3 += [((a3, 0), (4, 6), "0110", 2),
           ((a3, 1), (5, 5), "1011", 1), ((a3, 1), (5, 5), "1101", 3),
           ((a3, 1), (6, 4), "1100", 3),
           ((a3, 2), (6, 4), "0110", 3),
           ((a3, 3), (4, 6), "1100", 2),
           ((a3, 3), (5, 5), "1011", 0), ((a3, 3), (5, 5), "1101", 2)]
C3 += [((1, 0), (6, 4), "0000", 0), ((1, 0), (7, 3), "0001", 0),
       ((1, 2), (3, 7), "0001", 1), ((1, 2), (4, 6), "0000", 1)]
C4 = [
    ((0, 1), (3, 7), "0111", 0), ((0, 1), (4, 6), "0101", 0),
    ((0, 3), (6, 4), "0101", 2), ((0, 3), (7, 3), "0111", 2),
    ((1, 0), (6, 4), "0000", 3), ((1, 2), (4, 6), "0000", 1),
    ((1, 1), (5, 5), "0010", 3), ((1, 1), (6, 4), "1010", 3),
    ((1, 3), (4, 6), "1010", 1), ((1, 3), (5, 5), "0010", 1),
    ((2, 0), (4, 6), "1001", 0), ((2, 0), (5, 5), "1110", 1),
    ((2, 0), (6, 4), "1100", 1),
    ((3, 2), (4, 6), "1100", 3), ((3, 2), (5, 5), "1110", 3),
    ((3, 2), (6, 4), "1001", 2),
    ((2, 1), (5, 5), "1011", 2), ((3, 3), (5, 5), "1011", 0),
    ((2, 2), (5, 5), "0001", 0), ((2, 2), (6, 4), "0000", 0),
    ((3, 0), (4, 6), "0000", 2), ((3, 0), (5, 5), "0001", 2),
]
CLAIM_LOCI = {"wt-16": C2, "wt-18a": C3, "wt-18b": C4}
for key in ORBKEYS[:3]:
    name = ONAME[key]
    got = []
    for a3 in range(4):
        for a4 in range(4):
            for (V0, gamma), (lm, rm) in CELL_SUMS[(key, a3, a4)].items():
                if lm + rm == 10:
                    got.append(((a3, a4), (lm, rm),
                                "".join(str(b) for b in V0), gamma))
    check(f"{name}: locus table matches Appendix C ({len(got)} loci)",
          sorted(got) == sorted(CLAIM_LOCI[name]))

print("=== K3 / K4: achievers, structure lemma, and the kills ===")
CLAIM_COUNTS = {"wt-16": 48, "wt-18a": 48, "wt-18b": 22}
total_both, total_one, total_surv = 0, 0, 0
for key in ORBKEYS[:3]:
    name = ONAME[key]
    offs = ORB_DATA[key]
    achievers = []
    structure_ok = True
    for a3 in range(4):
        for a4 in range(4):
            b3L = xor4(offs[3][0], smul(a3, BH[3]))
            b3R = xor4(offs[3][1], smul(a3, AH[3]))
            b4Lc = xor4(offs[4][0], smul(W, smul(a4, AH[4])))
            b4Rc = xor4(offs[4][1], smul(a4, AH[4]))
            for gamma in range(4):
                V4L = xor4(b4Lc, smul(f4m(W, gamma), XYr))
                V4R = xor4(b4Rc, smul(gamma, XYr))
                for V0 in ALL_F2:
                    lm, rm = CELL_SUMS[(key, a3, a4)][(V0, gamma)]
                    Ls, Rs = [], []
                    for d3 in range(4):
                        V3 = xor4(b3L, smul(d3, XYr))
                        for V2 in IMR2:
                            c = sum(int(M1[V0[s], V2[s], V3[s], V4L[s]])
                                    for s in range(4))
                            if c <= 7:
                                Ls.append((c, V3, V2))
                    for d3 in range(4):
                        V3 = xor4(b3R, smul(d3, XYr))
                        for V1 in IMR1:
                            c = sum(int(M2[V0[s], V1[s], V3[s], V4R[s]])
                                    for s in range(4))
                            if c <= 7:
                                Rs.append((c, V3, V1))
                    pairs = [(L, R) for L in Ls for R in Rs
                             if L[0] + R[0] == 10]
                    # K4: achiever-structure lemma at this (V0, gamma)
                    if lm + rm == 10:
                        argL = [L for L in Ls if L[0] == lm]
                        argR = [R for R in Rs if R[0] == rm]
                        if sorted(pairs) != sorted((L, R) for L in argL
                                                   for R in argR):
                            structure_ok = False
                    elif pairs:
                        structure_ok = False
                    for (cL, V3L, V2L), (cR, V3R, V1R) in pairs:
                        achievers.append((V0, gamma, V2L, V3L, V4L,
                                          V1R, V3R, V4R))
    check(f"{name}: achiever count = {CLAIM_COUNTS[name]}",
          len(achievers) == CLAIM_COUNTS[name])
    check(f"{name}: achiever-structure lemma (argmin products)",
          structure_ok)
    for (V0, gamma, V2L, V3L, V4L, V1R, V3R, V4R) in achievers:
        min1 = []
        for s in range(4):
            mv = int(M1[V0[s], V2L[s], V3L[s], V4L[s]])
            min1.append([v1 for v1 in range(4)
                         if int(WT[V0[s], v1, V2L[s], V3L[s], V4L[s]]) == mv])
        min2 = []
        for s in range(4):
            mv = int(M2[V0[s], V1R[s], V3R[s], V4R[s]])
            min2.append([v2 for v2 in range(4)
                         if int(WT[V0[s], V1R[s], v2, V3R[s], V4R[s]]) == mv])
        t0 = next(t for t in ALL_F4 if ring_mul4(rho1, t) == V1R)
        ok1 = any(all(xor4(t0, k)[s] in min1[s] for s in range(4))
                  for k in KER1)
        u0 = next(t for t in ALL_F4 if ring_mul4(rho2, t) == V2L)
        ok2 = any(all(xor4(u0, k)[s] in min2[s] for s in range(4))
                  for k in KER2)
        if ok1 and ok2:
            total_surv += 1
        elif ok1 or ok2:
            total_one += 1
        else:
            total_both += 1
check("kills: 116 fail both links, 2 fail exactly one, 0 survive",
      (total_both, total_one, total_surv) == (116, 2, 0))

# the §13 worked kill: rho1 * (1,0,0,w2) = (w,1,0,w2) != (w2,w,0,1)
got = ring_mul4(rho1, (1, 0, 0, 3))
check("worked kill: rho1*(1,0,0,w2) = (w,1,0,w2) != V1R = (w2,w,0,1)",
      got == (2, 1, 0, 3) and got != (3, 2, 0, 1))

print()
if FAILURES:
    print(f"FAILURES ({len(FAILURES)}):")
    for f_ in FAILURES:
        print(f"  - {f_}")
    raise SystemExit(1)
print("ALL CHECKS PASS.")

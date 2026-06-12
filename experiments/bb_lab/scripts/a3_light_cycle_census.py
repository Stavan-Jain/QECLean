"""A3 / Track 1.1 Entry 21 — the light-cycle census: weights 6, 8, 10 with flux.

Route-B sizing + an independent cross-check of Entry 20.  By the flux
characterization (Entries 17-18), (M-im) is equivalent to: **every
non-boundary 1-cycle of weight <= 10 has nonzero seam flux** (cycle
weights are even; weights <= 5 are excluded by the small-cycle theorem;
weight 6 is the proven sub-rung).  This script enumerates ALL base
1-cycles w = (u_L, u_R) (A u_L = B u_R) of weights 6, 8, 10 exactly, by
split (|u_L|, |u_R|):

  - pure splits (w, 0) / (0, w): direct enumeration of Ann(A) / Ann(B)
    (both 12-dimensional, 4096 elements);
  - mixed splits with small side b <= 4: enumerate the small side,
    solve the 36x36 affine system on the heavy side (consistency via
    the row-ops matrix tail, particular solution from the pivots), scan
    the 4096-element solution coset for the target weight with packed
    popcounts;
  - the (5,5) split: syndrome hash-join over C(36,5) = 376992 per side.

Per cycle: the six seam-flux parities ell_xi(w) = xi^T d1c_0 w (xi in
ker H_X^T), and boundary membership w in im d2 (42-bit syndrome key K).
Tallies per weight: total, boundaries, flux-silent non-boundaries
(MUST be 0 — this re-proves (M-im) at weights 8/10 by a route fully
independent of Entry 20's value grammar), split distribution,
translation-orbit counts of the non-boundary cycles (the route-B
hand-census size), and the flux-vector counts.

Sanity ladder (before trusting weights 8/10):
  C1  Ann dims = 12, min weights 6 (the W1 Ann-engine anchor);
  C2  weight-6 reproduction: exactly 120 cycles = 36 hexagons
      (boundaries, flux-silent) + 84 logicals (all flux-loud), splits
      36/48/36 over (6,0)/(3,3)/(0,6) — the Entry-13/16/17 ground truth;
  C3  the weight-10 boundaries are exactly the 216 D-pairs with splits
      (4,6)/(6,4) (Entry-9 ground truth);
  C4  flux is class-invariant on samples (w and w + d2 t agree);
  C5  solver spot-checks (M x0 = s on random small-side syndromes).

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import combinations

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
MA = d2b[nb:, :]                       # multiplication by A (36 x 36)
MB = d2b[:nb, :]                       # multiplication by B

A_steps = [(3, 0), (0, 1), (0, 2)]
B_steps = [(0, 3), (1, 0), (2, 0)]


def d1c_mat(j):
    d1c = np.zeros((nb, 2 * nb), np.uint8)
    for blk, steps in ((0, A_steps), (1, B_steps)):
        for g in Gb:
            col = blk * nb + Gb.index(g)
            for (sx, sy) in steps:
                if ((g[0] - j) % 6) + sx >= 6:
                    d1c[Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6)), col] ^= 1
    return d1c


D1C0 = d1c_mat(0)
K0 = nullspace_f2(HX.T)                # the six flux functionals
K = nullspace_f2(d2b.T)                # 42-bit boundary key
FLUXM = (K0 @ D1C0) % 2                # 6 x 72: flux(w) = FLUXM w
assert K0.shape[0] == 6 and K.shape[0] == 42

# ------------------------------------------------------------- bit packing
BITPOS = [np.uint64(1) << np.uint64(nb - 1 - i) for i in range(nb)]


def pack_vec(v):
    out = np.uint64(0)
    for i in range(nb):
        if v[i]:
            out |= BITPOS[i]
    return out


def unpack_bits(bits):
    return np.array([(int(bits) >> (nb - 1 - i)) & 1 for i in range(nb)],
                    np.uint8)


try:
    np.bitwise_count(np.uint64(3))

    def popcnt(arr):
        return np.bitwise_count(arr)
except AttributeError:
    _PC = np.array([bin(i).count("1") for i in range(256)], np.uint16)

    def popcnt(arr):
        return _PC[np.ascontiguousarray(arr).view(np.uint8)
                   .reshape(arr.shape + (8,))].sum(-1)


# ------------------------------------------------- affine solver for MA, MB
def make_solver(M):
    """(T, piv): T M = R in rref with pivot columns piv; M x = s solvable
    iff (T s)[len(piv):] = 0, one solution x[piv[i]] = (T s)[i]."""
    m = M.shape[0]
    aug = np.concatenate([M.copy() % 2, np.eye(m, dtype=np.uint8)], axis=1)
    r = 0
    piv = []
    for c in range(M.shape[1]):
        rows = [i for i in range(r, m) if aug[i, c]]
        if not rows:
            continue
        if rows[0] != r:
            aug[[r, rows[0]]] = aug[[rows[0], r]]
        for i in range(m):
            if i != r and aug[i, c]:
                aug[i] ^= aug[r]
        piv.append(c)
        r += 1
    return aug[:, M.shape[1]:] % 2, piv


TA, pivA = make_solver(MA)
TB, pivB = make_solver(MB)
kerA = nullspace_f2(MA)
kerB = nullspace_f2(MB)

print("=== C1: Ann anchors ===")
print(f"  dim Ann(A) = {kerA.shape[0]}, dim Ann(B) = {kerB.shape[0]} (claim 12)")


def all_span(rows):
    n = rows.shape[0]
    out = np.zeros((1 << n, rows.shape[1]), np.uint8)
    for i in range(n):
        step = 1 << i
        out[step:2 * step] = out[:step] ^ rows[i]
    return out


ANN_A = all_span(kerA)
ANN_B = all_span(kerB)
wtA = ANN_A.sum(1)
wtB = ANN_B.sum(1)
print(f"  Ann(A) weights <= 10: "
      f"{ {int(w): int((wtA == w).sum()) for w in sorted(set(wtA)) if 0 < w <= 10} }")
print(f"  Ann(B) weights <= 10: "
      f"{ {int(w): int((wtB == w).sum()) for w in sorted(set(wtB)) if 0 < w <= 10} }")
ANN_A_PK = np.array([pack_vec(v) for v in ANN_A], np.uint64)
ANN_B_PK = np.array([pack_vec(v) for v in ANN_B], np.uint64)

# T-images of the opposite block's columns (solve linearity in s)
TA_BCOL = [(TA @ MB[:, i]) % 2 for i in range(nb)]
TB_ACOL = [(TB @ MA[:, i]) % 2 for i in range(nb)]

print("\n=== C5: solver spot-checks ===")
rng = np.random.default_rng(20260612)
ok_c5 = True
for _ in range(50):
    t = rng.integers(0, 2, nb, dtype=np.uint8)
    s = (MB @ t) % 2                  # consistent by construction? not nec.
    y = (TA @ s) % 2
    if not y[len(pivA):].any():
        x0 = np.zeros(nb, np.uint8)
        for i, c in enumerate(pivA):
            x0[c] = y[i]
        ok_c5 &= ((MA @ x0) % 2 == s).all()
print(f"  MA x0 = s on consistent random syndromes: {ok_c5}")

# ------------------------------------------------------------- the census
PERM_INV = {}
for dx in range(6):
    for dy in range(6):
        idx = np.empty(nb, np.int64)
        for g in Gb:
            idx[Gb.index(g)] = Gb.index(((g[0] - dx) % 6, (g[1] - dy) % 6))
        PERM_INV[(dx, dy)] = idx


def census_weight(target):
    """All cycles of the given total weight, as packed (uL, uR) pairs."""
    found = {}

    def record(uLb, uRb):
        found[(int(uLb), int(uRb))] = True

    for v in ANN_A[wtA == target]:
        record(pack_vec(v), 0)
    for v in ANN_B[wtB == target]:
        record(0, pack_vec(v))
    # mixed splits with small side b <= 4
    for b in range(1, min(4, target // 2) + 1):
        a = target - b
        # small RIGHT side: |u_R| = b, solve MA u_L = MB u_R, |u_L| = a
        for comb in combinations(range(nb), b):
            y = TA_BCOL[comb[0]].copy()
            for i in comb[1:]:
                y ^= TA_BCOL[i]
            if y[len(pivA):].any():
                continue
            x0b = np.uint64(0)
            for i, c in enumerate(pivA):
                if y[i]:
                    x0b |= BITPOS[c]
            hits = np.flatnonzero(popcnt(ANN_A_PK ^ x0b) == a)
            if hits.size:
                uRb = np.uint64(0)
                for i in comb:
                    uRb |= BITPOS[i]
                for k in hits:
                    record(ANN_A_PK[k] ^ x0b, uRb)
        if a == b:
            continue                   # the left pass would duplicate
        # small LEFT side: |u_L| = b, solve MB u_R = MA u_L, |u_R| = a
        for comb in combinations(range(nb), b):
            y = TB_ACOL[comb[0]].copy()
            for i in comb[1:]:
                y ^= TB_ACOL[i]
            if y[len(pivB):].any():
                continue
            x0b = np.uint64(0)
            for i, c in enumerate(pivB):
                if y[i]:
                    x0b |= BITPOS[c]
            hits = np.flatnonzero(popcnt(ANN_B_PK ^ x0b) == a)
            if hits.size:
                uLb = np.uint64(0)
                for i in comb:
                    uLb |= BITPOS[i]
                for k in hits:
                    record(uLb, ANN_B_PK[k] ^ x0b)
    # the (5,5) split via hash-join
    if target == 10:
        side = {}
        for comb in combinations(range(nb), 5):
            s = np.uint64(0)
            for i in comb:
                s ^= ACOL_PK[i]
            side.setdefault(int(s), []).append(comb)
        for comb in combinations(range(nb), 5):
            s = np.uint64(0)
            for i in comb:
                s ^= BCOL_PK[i]
            for combL in side.get(int(s), ()):
                uLb = np.uint64(0)
                for i in combL:
                    uLb |= BITPOS[i]
                uRb = np.uint64(0)
                for i in comb:
                    uRb |= BITPOS[i]
                record(uLb, uRb)
    return list(found)


ACOL_PK = [pack_vec(MA[:, i]) for i in range(nb)]
BCOL_PK = [pack_vec(MB[:, i]) for i in range(nb)]


def unpack72(uLb, uRb):
    w = np.zeros(72, np.uint8)
    w[:nb] = unpack_bits(uLb)
    w[nb:] = unpack_bits(uRb)
    return w


def flux_of(w72):
    return tuple(int(v) for v in (FLUXM @ w72) % 2)


def is_boundary(w72):
    return not ((K @ w72) % 2).any()


def analyze(target):
    cyc = census_weight(target)
    n_bd = 0
    silent_nonbd = []
    loud = []
    splits = {}
    for uLb, uRb in cyc:
        w = unpack72(uLb, uRb)
        assert not ((HX @ w) % 2).any(), "census produced a non-cycle!"
        assert int(w.sum()) == target
        sp = (bin(uLb).count("1"), bin(uRb).count("1"))
        splits[sp] = splits.get(sp, 0) + 1
        fx = flux_of(w)
        if is_boundary(w):
            n_bd += 1
        elif not any(fx):
            silent_nonbd.append((uLb, uRb))
        else:
            loud.append((uLb, uRb, fx))
    orb = {}
    for uLb, uRb, fx in loud:
        vL, vR = unpack_bits(uLb), unpack_bits(uRb)
        key = min((vL[PERM_INV[d]].tobytes() + vR[PERM_INV[d]].tobytes())
                  for d in PERM_INV)
        orb.setdefault(key, []).append(fx)
    print(f"\n  weight {target}: {len(cyc)} cycles; "
          f"splits {dict(sorted(splits.items()))}")
    print(f"    boundaries: {n_bd}; non-boundaries: "
          f"{len(loud) + len(silent_nonbd)}; FLUX-SILENT non-boundaries: "
          f"{len(silent_nonbd)} (claim 0)")
    print(f"    non-boundary translation orbits: {len(orb)}; "
          f"orbit sizes {sorted(len(v) for v in orb.values())}")
    return cyc, silent_nonbd, orb


print("\n=== C2: weight-6 reproduction (ground truth) ===")
cyc6, silent6, orb6 = analyze(6)
ok_c2 = (len(cyc6) == 120 and len(silent6) == 0)
print(f"  C2 PASS (120 cycles, no silent non-boundaries): {ok_c2}")

print("\n=== C4: flux is class-invariant (samples) ===")
ok_c4 = True
for uLb, uRb in cyc6[:10]:
    w = unpack72(uLb, uRb)
    for _ in range(20):
        t = rng.integers(0, 2, nb, dtype=np.uint8)
        ok_c4 &= (flux_of((w + d2b @ t) % 2) == flux_of(w))
print(f"  flux(w + d2 t) == flux(w) on 10 cycles x 20 boundaries: {ok_c4}")

print("\n=== the weight-8 and weight-10 censuses ===")
cyc8, silent8, orb8 = analyze(8)
cyc10, silent10, orb10 = analyze(10)

print("\n=== C3: weight-10 boundary cross-check ===")
sp10 = {}
for uLb, uRb in cyc10:
    if is_boundary(unpack72(uLb, uRb)):
        sp = (bin(uLb).count("1"), bin(uRb).count("1"))
        sp10[sp] = sp10.get(sp, 0) + 1
print(f"  weight-10 boundaries: {sum(sp10.values())} with splits "
      f"{dict(sorted(sp10.items()))} (claim 216, (4,6)+(6,4))")

verdict = (len(silent8) == 0 and len(silent10) == 0)
print(f"\n  VERDICT — no flux-silent non-boundary cycles at weights 8, 10: "
      f"{verdict}")
print("  (with the weight-6 sub-rung and the small-cycle theorem this "
      "re-proves (M-im)\n   by the flux route, independently of the "
      "Entry-20 value grammar)")

print("\nDone.")

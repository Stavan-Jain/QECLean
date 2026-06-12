"""A3 / Track 1.1 Entry 13 — the small-cycle theorem and its intermediates.

Machine-verification of every step in the hand proof that the base
[[72,12,6]] code has NO nonzero 1-cycles (ker H_X) of weight <= 5, and of
its mirror for ker H_Z.  Consequences verified downstream: the two m-rung
locality facts (m(hexagon) >= 3, m(D-pair) >= 1) and the discharge of (H0)
d_base >= 6 — the b = 0 rung input.

A 1-cycle is u = (u_L, u_R) with A·u_L = B·u_R (group-algebra products over
F2[Z6^2]); weight splits (|u_L|, |u_R|).  The hand proof kills each split:

  W1  Ann(A), Ann(B) have min weight 6 (engine: units kill z0, z2-hat; the
      radical components are self-annihilating ideals with co-point-or-full
      support => >= 3 alive layers, all even => weight >= 6).
      Kills (0,k)/(k,0) for k <= 5.
  W2  parity |A u_L| = |u_L|, |B u_R| = |u_R| mod 2 kills odd-vs-even splits
      (1,2), (2,1), (1,4), (4,1), (2,3), (3,2).
  W3  (1,1): A·g = B·r would force the translate sets to coincide, hence
      dA = dB; but dA cap dB = empty.
  W4  (1,3)/(3,1): |B(3-set)| = 3 forces a dB-triangle (all pairwise diffs
      in dB, no common triple cell).  dB-triangles are ONE class up to
      translation+reflection (two up to translation): the chirality with a
      common triple cell has |Bz| = 7 (dead); the other has Bz = a translate
      of y^3(1+x^2+x^4) — constant y-coordinate — while every A·g has three
      distinct y-coordinates (dead).  Mirror for dA-triangles (constant x
      vs three distinct x for B·r).
  W5  (2,2): sub-cases by the x/y projections pi_x, pi_y (ring homs to
      F2[Z6], pi_y(A) = 1+y+y^2, pi_y(B) = y^3, pi_x(A) = x^3,
      pi_x(B) = 1+x+x^2):
      |sigma| = 4 (both pairs overlapping): ell-diff in dA with y-gap 1
      (else pi_y weights mismatch); ell-diff = (0,+-1) forces r-diff = (0,3)
      not in dB via Ann(1+x+x^2) min weight 4; ell-diff = (3,+-1) forces
      r-diff = +-(1,3), and then the x-coordinate multiplicity multisets
      differ: sigma_A has {3,1}, sigma_B has {2,1,1} (translation-invariant).
      |sigma| = 6 (both pairs disjoint): pi_y/pi_x weight bookkeeping forces
      r-diff = (+-1, 0) in dB or weight mismatches — all dead.
  W6  exhaustive confirmation: hash-join over ALL splits a+b <= 5 finds NO
      nonzero cycle on either side (ker H_X and ker H_Z).
  W7  weight-6 census cross-check: exactly 120 weight-6 cycles in ker H_X
      (= 36 hexagons + 84 logicals, the T4 numbers).
  W8  the m-rung scaffolding: supp(d2c_j delta_g) subset h(g) for every g
      and cut j (the seam split is entrywise), and |h(g) cap h(g')| = 1 for
      D-pairs — the inputs to the four-coset averaging argument.

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
cm = bb_check_matrices(Ab, Bb)
HX = (cm.H_X & 1)
HZ = (cm.H_Z & 1)
d2b = HZ.T
nb = 36
# H_X = (M_A | M_B): columns 0..35 are left qubits (syndrome A·delta),
# 36..71 right (B·delta).  H_Z = (M_B^T | M_A^T).
MA_cols = HX[:, :nb]                              # column g = A.delta_g
MB_cols = HX[:, nb:]
MBT_cols = HZ[:, :nb]                             # column g = Bbar.delta_g
MAT_cols = HZ[:, nb:]

def col_ints(M):
    return [int("".join(str(b) for b in M[:, i]), 2) for i in range(M.shape[1])]

def col_syndromes(M, k):
    """dict syndrome-int -> count over all k-subsets of columns of M."""
    cols = col_ints(M)
    out = {}
    def rec(start, depth, acc):
        if depth == k:
            out[acc] = out.get(acc, 0) + 1
            return
        for i in range(start, len(cols) - (k - depth - 1)):
            rec(i + 1, depth + 1, acc ^ cols[i])
    rec(0, 0, 0)
    return out

# ------------------------------------------------- W1: annihilator minima
print("=== W1: Ann(A) and Ann(B) minima (engine consequence) ===")
A_map = d2b[nb:, :]
B_map = d2b[:nb, :]
def span_weights(rows):
    ws = {}
    for mask in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (mask >> i) & 1:
                v ^= rows[i]
        w = int(v.sum())
        ws[w] = ws.get(w, 0) + 1
    return ws
wA = span_weights(nullspace_f2(A_map))
wB = span_weights(nullspace_f2(B_map))
print(f"  Ann(A): min nonzero weight = {min(w for w in wA if w)} (claim 6); "
      f"all weights even: {all(w % 2 == 0 for w in wA)}")
print(f"  Ann(B): min nonzero weight = {min(w for w in wB if w)} (claim 6); "
      f"all weights even: {all(w % 2 == 0 for w in wB)}")

# --------------------------------------------------------- W3: (1,1) split
print("\n=== W3: (1,1) — translate sets never coincide ===")
SA1 = col_syndromes(MA_cols, 1)
SB1 = col_syndromes(MB_cols, 1)
print(f"  {{A.g}} cap {{B.r}} empty: {not (set(SA1) & set(SB1))}")

# ------------------------------------------- W4: (1,3)/(3,1) — triangles
print("\n=== W4: dB-triangles (and mirror dA) ===")
def diffset(supp):
    return {((g1[0] - g2[0]) % 6, (g1[1] - g2[1]) % 6)
            for g1 in supp for g2 in supp if g1 != g2}
dA = diffset([(3, 0), (0, 1), (0, 2)])
dB = diffset([(0, 3), (1, 0), (2, 0)])

def triangles(D):
    """All {0,a,b} with a, b, b-a in D, as canonical translate classes."""
    tris = set()
    for a in D:
        for b in D:
            if a == b:
                continue
            if ((b[0] - a[0]) % 6, (b[1] - a[1]) % 6) in D:
                cells = [(0, 0), a, b]
                canon = min(tuple(sorted((((c[0] - t[0]) % 6, (c[1] - t[1]) % 6))
                                         for c in cells)) for t in cells)
                tris.add(canon)
    return tris

def gp_mul_set(supp, z_cells):
    out = set()
    for s in supp:
        for z in z_cells:
            c = ((s[0] + z[0]) % 6, (s[1] + z[1]) % 6)
            out ^= {c}
    return out

triB = triangles(dB)
print(f"  dB-triangle classes up to translation: {len(triB)} (claim 2 = one chirality pair)")
suppB = [(0, 3), (1, 0), (2, 0)]
suppA = [(3, 0), (0, 1), (0, 2)]
for tri in sorted(triB):
    img = gp_mul_set(suppB, tri)
    ys = {c[1] for c in img}
    print(f"    triangle {tri}: |B.z| = {len(img)}"
          + (f", constant-y: {len(ys) == 1}" if len(img) == 3 else " (dead: != 3)"))
ysA = [len({c[1] for c in gp_mul_set(suppA, [g])}) for g in [(0, 0), (1, 2), (5, 4)]]
print(f"  every A.g has 3 distinct y-coordinates: {all(v == 3 for v in ysA)} "
      f"(checked on sample translates; structural: y-parts of A are 0,1,2)")
triA = triangles(dA)
print(f"  dA-triangle classes: {len(triA)}; images:")
for tri in sorted(triA):
    img = gp_mul_set(suppA, tri)
    xs = {c[0] for c in img}
    print(f"    triangle {tri}: |A.z| = {len(img)}"
          + (f", constant-x: {len(xs) == 1}" if len(img) == 3 else " (dead: != 3)"))

# ------------------------------------------------------- W5: (2,2) split
print("\n=== W5: (2,2) intermediates ===")
sigA = gp_mul_set(suppA, [(0, 0), (3, 1)])
def xmultiset(cells):
    from collections import Counter
    return tuple(sorted(Counter(c[0] for c in cells).values()))
sigB1 = gp_mul_set(suppB, [(0, 0), (1, 3)])
print(f"  sigma_A = A(1 + x^3y): weight {len(sigA)}, x-multiplicity multiset "
      f"{xmultiset(sigA)} (claim (1,3))")
print(f"  sigma_B = B(1 + xy^3): weight {len(sigB1)}, x-multiplicity multiset "
      f"{xmultiset(sigB1)} (claim (1,1,2)); distinct from sigma_A's: "
      f"{xmultiset(sigA) != xmultiset(sigB1)}")
# Ann(1+x+x^2) in F2[Z6] has min weight 4 (so a 2-set cannot annihilate it)
poly = np.zeros(6, np.uint8); poly[[0, 1, 2]] = 1
ann_wts = []
for mask in range(1, 64):
    f = np.array([(mask >> i) & 1 for i in range(6)], np.uint8)
    conv = np.zeros(6, np.uint8)
    for i in range(6):
        if f[i]:
            conv ^= np.roll(poly, i)
    if not conv.any():
        ann_wts.append(int(f.sum()))
print(f"  Ann(1+x+x^2) in F2[Z6]: min weight = {min(ann_wts)} (claim 4)")

# --------------------------------------- W6: exhaustive small-cycle check
print("\n=== W6: exhaustive — no nonzero cycles of weight <= 5, both sides ===")
def no_small_cycles(ML, MR, wmax=5):
    SL = {k: col_syndromes(ML, k) for k in range(1, wmax + 1)}
    SR = {k: col_syndromes(MR, k) for k in range(1, wmax + 1)}
    zero = 0
    bad = 0
    for a in range(0, wmax + 1):
        for b in range(0, wmax + 1 - a):
            if a == 0 and b == 0:
                continue
            if a == 0:
                bad += SR[b].get(zero, 0)
            elif b == 0:
                bad += SL[a].get(zero, 0)
            else:
                common = set(SL[a]) & set(SR[b])
                bad += sum(SL[a][k] * SR[b][k] for k in common)
    return bad, SL, SR
badX, SLX, SRX = no_small_cycles(MA_cols, MB_cols)
badZ, _, _ = no_small_cycles(MBT_cols, MAT_cols)
print(f"  ker H_X: nonzero cycles of weight <= 5: {badX} (claim 0)")
print(f"  ker H_Z: nonzero cycles of weight <= 5: {badZ} (claim 0)")

# ------------------------------------------------- W7: weight-6 census
print("\n=== W7: weight-6 cycle census (cross-check vs T4) ===")
SL6 = dict(SLX); SL6[6] = col_syndromes(MA_cols, 6)
SR6 = dict(SRX); SR6[6] = col_syndromes(MB_cols, 6)
zero = 0
total = SL6[6].get(zero, 0) + SR6[6].get(zero, 0)
for a in range(1, 6):
    b = 6 - a
    common = set(SL6[a]) & set(SR6[b])
    total += sum(SL6[a][k] * SR6[b][k] for k in common)
print(f"  weight-6 cycles in ker H_X: {total} (claim 120 = 36 hexagons + 84 logicals)")

# ------------------------------------------------- W8: m-rung scaffolding
print("\n=== W8: seam-split containment and D-pair overlap ===")
print("  supp(d2c_j delta_g) subset h(g): the c/nc split is entrywise on d2 "
      "(each d2c entry is a d2 entry) — holds by construction")
hex_supports = {}
for g in Gb:
    z = np.zeros(nb, np.uint8); z[Gb.index(g)] = 1
    hex_supports[g] = frozenset(np.flatnonzero((d2b @ z) % 2))
ok_ov = True
D = dA | dB
for g in [(0, 0), (1, 4), (3, 2)]:
    for d in D:
        g2 = ((g[0] + d[0]) % 6, (g[1] + d[1]) % 6)
        ok_ov &= len(hex_supports[g] & hex_supports[g2]) == 1
print(f"  |h(g) cap h(g+delta)| = 1 for delta in D (samples x all D): {ok_ov}")

# ------------------------------------- W9: the iota X<->Z duality (cover too)
print("\n=== W9: inversion duality Phi: (wL, wR) -> (iota(wR), iota(wL)) ===")
def duality_check(G, Apoly, Bpoly):
    c = bb_check_matrices(Apoly, Bpoly)
    hx, hz = (c.H_X & 1), (c.H_Z & 1)
    n = hx.shape[1] // 2
    perm = np.zeros(2 * n, dtype=int)
    for g in G:
        gi = G.index(g)
        gj = G.index(G.neg(g))
        perm[gi] = n + gj                          # left slot <- iota(right)
        perm[n + gi] = gj                          # right slot <- iota(left)
    P = np.zeros((2 * n, 2 * n), np.uint8)
    for i, j in enumerate(perm):
        P[i, j] = 1
    kerZ = nullspace_f2(hz)
    ok = not ((hx @ ((kerZ @ P.T) % 2).T) % 2).any()   # Phi(ker H_Z) in ker H_X
    stackZ = np.vstack([hz, (hx @ P) % 2])
    from bb_lab.linalg import rank_f2
    ok &= rank_f2(stackZ) == rank_f2(hz)               # Phi(rowsp H_X) = rowsp H_Z
    return ok
okb = duality_check(Gb, Ab, Bb)
Gc = ZmZn(12, 6)
okc = duality_check(Gc, Poly.from_string("x^3 + y + y^2", Gc),
                    Poly.from_string("y^3 + x + x^2", Gc))
print(f"  base [[72,12,6]]: Phi(ker H_Z) = ker H_X and Phi(X-stabs) = Z-stabs: {okb}")
print(f"  cover [[144,12,12]] (gross): same: {okc}")
print("  => d_X = d_Z for both codes (weight-preserving class bijection)")

print("\nDone.")

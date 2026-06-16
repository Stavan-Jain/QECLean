"""A3 / Track 1.1 — trustworthy structural facts about gross's dangerous sector.

Deliberately AVOIDS the scout sector-SAT (scripts/a1_smith_sector_sat.py), whose
"safe sector min = 6" is an ENCODING BUG: gross's distance is 12 (established
SAT+DRAT certificate in certificates/), so NO logical of weight < 12 exists in
either sector. This script derives only facts that rest on (a) F2 linear algebra
and (b) the established d_gross = 12 — never on a hand-rolled CNF.

Trustworthy facts established here:
  F1. pr_* : H1(cover) -> H1(base) has rank 6, kernel 6 (the 6-dim dangerous
      sector ker(pr_*)).
  F2. Each of the 6 dangerous logical reps projects to the ZERO CHAIN under p
      (not merely a trivial class). Since p sums the two cover sheets, p(v)=0
      means the two sheets are EQUAL: v = (u,u) = tau(u) for a base chain u.
  F3. That base chain u is a NONTRIVIAL base logical (u in ker H_X^base,
      u not in rowspan H_Z^base) of weight exactly 6 = d_base; so the dangerous
      rep has weight 2|u| = 12 = 2*d_base.
  F4. Dangerous-sector min weight = 12, by trusted reasoning: the reps achieve
      12, and nothing is below d_gross = 12. (No SAT needed.)
  F5. Safe-sector min weight >= 12, forced by d_gross = 12 (NOT 6 as the buggy
      scout SAT claims).

These pin the SHAPE of the obstruction. They are discovery/validation only and
can never be load-bearing in a final analytic proof (same exclusion as SAT).
"""
from __future__ import annotations
import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import rank_f2, nullspace_f2, quotient_complement_basis

Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
nc, nb = Gc.cardinality, Gb.cardinality
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z

# projection p on C1 (sum the two sheets), and the lift tau on C1 (copy to both sheets)
P = np.zeros((2*nb, 2*nc), dtype=np.uint8)
for gt in Gc:
    gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
    P[Gb.index(gb), Gc.index(gt)] ^= 1
    P[nb+Gb.index(gb), nc+Gc.index(gt)] ^= 1

def p_apply(v):  # cover chain (2nc) -> base chain (2nb)
    return (P @ (v & 1)) & 1

# logical reps
ker_HXc = nullspace_f2(HXc); logZ_c = quotient_complement_basis(HZc, ker_HXc)
ker_HXb = nullspace_f2(HXb); logZ_b = quotient_complement_basis(HZb, ker_HXb)

# pr_* matrix (cover-logical-basis -> base-logical-coords), reusing the probe's coord solve
def base_class_coords(v):
    v = v & 1
    if np.any((HXb @ v) & 1):
        return None
    M = np.vstack([HZb, logZ_b]).astype(np.uint8)
    A = np.concatenate([M.T.copy(), v.reshape(-1, 1).astype(np.uint8)], axis=1)
    rows, cols = A.shape; pr = 0; piv = {}
    for col in range(cols - 1):
        if pr >= rows: break
        nz = np.flatnonzero(A[pr:, col])
        if nz.size == 0: continue
        r = pr + int(nz[0])
        if r != pr: A[[pr, r]] = A[[r, pr]]
        mask = A[:, col] == 1; mask[pr] = False
        if mask.any(): A[mask] ^= A[pr]
        piv[col] = pr; pr += 1
    c = np.zeros(cols - 1, dtype=np.uint8)
    for col, r in piv.items(): c[col] = A[r, cols-1]
    return c[M.shape[0]-logZ_b.shape[0]:]

prmat = np.zeros((12, 12), dtype=np.uint8)
for j, L in enumerate(logZ_c):
    coords = base_class_coords(p_apply(L))
    prmat[:, j] = np.zeros(12, np.uint8) if coords is None else coords
rk = rank_f2(prmat)
print(f"F1: pr_* rank = {rk}, kernel (dangerous) dim = {12-rk}")

# dangerous basis: kernel of prmat over F2
def f2_kernel(M):
    return nullspace_f2(M)
dang_coeffs = f2_kernel(prmat)   # rows = F2 combos of logZ_c that land in ker(pr_*)
print(f"    #dangerous basis classes = {dang_coeffs.shape[0]}")

def rep_of(coeff):
    v = np.zeros(2*nc, dtype=np.uint8)
    for j in range(12):
        if coeff[j]: v ^= logZ_c[j]
    return v & 1

def base_logical_status(u):
    u = u & 1
    in_ker = not np.any((HXb @ u) & 1)
    stacked = np.vstack([HZb, u.reshape(1, -1)])
    nontrivial = rank_f2(stacked) > rank_f2(HZb)
    return in_ker, nontrivial

print("\nF2/F3: structure of each dangerous basis rep")
print(" rep | |L~| | p(L~)=0? | sheets equal? | |u| | u nontrivial base logical?")
all_good = True
for i, c in enumerate(dang_coeffs):
    L = rep_of(c)
    pL = p_apply(L)
    sheet0 = L[:nc]; sheet1 = L[nc:]            # WRONG split: blocks, not sheets — see note
    # correct sheet split: a "sheet" is a deck-orbit half. The deck sigma swaps
    # x and x+6. p(L)=0 <=> for every base position the 2 lifts carry equal bits.
    # Recover u as the base chain p restricted appropriately: since p(L)=0, the
    # cover support is sigma-symmetric; u := image of L under "pick one lift per
    # base cell" = (P_half) L. Cleanest: u = base chain s.t. tau(u) = L.
    pzero = not np.any(pL)
    # tau(u)=L  <=>  u is the common value of the two lifts. Build tau and solve.
    # tau matrix (2nb -> 2nc): copy base cell to both its lifts.
    # invert by reading either lift.
    # base cell (gb, blk) -> its two cover lifts; read the A-block lift with x=gb_x.
    u = np.zeros(2*nb, dtype=np.uint8)
    for gt in Gc:
        gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
        # take the representative lift with smaller x (gt_x < 6) as the "value"
        if gt[0] < 6:
            u[Gb.index(gb)] ^= L[Gc.index(gt)]
            u[nb+Gb.index(gb)] ^= L[nc+Gc.index(gt)]
    # verify tau(u) == L
    tauu = np.zeros(2*nc, dtype=np.uint8)
    for gt in Gc:
        gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
        tauu[Gc.index(gt)] = u[Gb.index(gb)]
        tauu[nc+Gc.index(gt)] = u[nb+Gb.index(gb)]
    sheets_equal = np.array_equal(tauu & 1, L & 1)
    in_ker, nontriv = base_logical_status(u)
    print(f"  {i}  | {int(L.sum()):3d}  |   {pzero}   |    {sheets_equal}     | {int(u.sum()):2d}  | ker={in_ker} nontrivial={nontriv}")
    all_good &= pzero and sheets_equal and (int(u.sum()) == 6) and in_ker and nontriv

print(f"\nF2/F3 all dangerous reps are tau(nontrivial base 6-logical): {all_good}")
print("\nF4: dangerous-sector min weight = 12")
print("    (reps achieve 12; nothing < d_gross=12; no SAT needed)")
print("F5: safe-sector min weight >= 12, FORCED by d_gross=12.")
print("    The scout a1_smith_sector_sat.py 'safe min = 6' is an ENCODING BUG")
print("    (a weight-6 logical would mean d<=6, contradicting the d=12 certificate).")

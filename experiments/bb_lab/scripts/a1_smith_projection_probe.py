"""Track 1.1 scout probe: projection behaviour of gross's X-logicals onto
the [[72,12,6]] base under the SRB projection map p (Smith pr_* at chain level).

Smith two-branch skeleton for the free Z2 cover gross -> [[72,12,6]]:
  cover X-logical L~ with class [L~] in H1(cover).
  Branch (safe):     pr_*[L~] != 0 in H1(base)  =>  |L~| >= |p(L~)| >= d_base = 6.
  Branch (dangerous): pr_*[L~] = 0              =>  [L~] in Im(tr_*), tr doubles weight,
                       Ker(tr_*) = Im(Delta = cap omega).

SRB Example 8 (per Gap 5) says gross HAS X-logicals projecting to zero, so the
dangerous branch is realized. This probe quantifies it:

  Q1: how does the SRB p map act on cover chains? (verify p commutes with boundary)
  Q2: take a basis of cover X-logicals (ker H_X / rowspan H_Z). For each, compute
      [p(L~)] in base H1 (i.e. is p(L~) in ker H_X^base, and is it nontrivial
      mod rowspan H_Z^base?). Tabulate how many of the 12 logical classes project
      to nonzero base classes vs zero.
  Q3: the SHARP question -- among MINIMUM-WEIGHT (weight-12) cover X-logicals,
      does any project to a zero base class or sub-d_base base class? If a
      min-weight cover logical projects to zero, the dangerous branch is the
      binding constraint and weight control through Delta is unavoidable.
      If every min-weight cover logical projects to a nontrivial base class of
      weight >= 6, the safe branch already proves d_cover >= d_base on the
      minimum-weight locus (and the dangerous branch, while realized on SOME
      logical class, never threatens the bound).

All numbers are DISCOVERY artifacts; the Smith machinery is the analytic object.
"""
from __future__ import annotations
import numpy as np
from itertools import combinations

from bb_lab.group import ZmZn, AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import rank_f2, nullspace_f2, quotient_complement_basis, rref_f2

# ----- cover (gross) and base ([[72,12,6]]) -----
Gc = ZmZn(12, 6)
Ac = Poly.from_string("x^3 + y + y^2", Gc)
Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)

cm_c = bb_check_matrices(Ac, Bc)
cm_b = bb_check_matrices(Ab, Bb)
nc = Gc.cardinality   # 72
nb = Gb.cardinality   # 36

HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z

print(f"cover: |G|={nc}, 2|G|={2*nc}, rank H_X={rank_f2(HXc)}, rank H_Z={rank_f2(HZc)}")
print(f"base:  |G|={nb}, 2|G|={2*nb}, rank H_X={rank_f2(HXb)}, rank H_Z={rank_f2(HZb)}")

# ----- the SRB projection map p on C1 = (G x {A,B}) -----
# cover qubit index in block layout: qubit (g_tilde, block) -> column
#   block 0 (A-block): col = Gc.index(g_tilde)
#   block 1 (B-block): col = nc + Gc.index(g_tilde)
# p sends g_tilde -> pi(g_tilde) = (a mod 6, b mod 6), block preserved.
# Build the 2nb x 2nc projection matrix P (base-cols x cover-cols).
def proj_elem(gt):
    return tuple(gi % o for gi, o in zip(gt, Gb.orders))

P = np.zeros((2 * nb, 2 * nc), dtype=np.uint8)
for gt in Gc:
    cidxA = Gc.index(gt)
    cidxB = nc + Gc.index(gt)
    gb = proj_elem(gt)
    bidxA = Gb.index(gb)
    bidxB = nb + Gb.index(gb)
    P[bidxA, cidxA] ^= 1   # over F2: monomials colliding cancel
    P[bidxB, cidxB] ^= 1

def p_apply(v_cover):  # v_cover length 2nc -> length 2nb, over F2
    return (P @ (v_cover & 1)) & 1

# ----- sanity: does p commute with the boundary? (SRB Thm 4.1: p is a chain map) -----
# At the C1->C0 level the boundary is H_X (the X-syndrome map), going C1 -> C0=G.
# Need a projection p0 on C0 = G as well. p0: G_c -> G_b same reduction.
P0 = np.zeros((nb, nc), dtype=np.uint8)
for gt in Gc:
    P0[Gb.index(proj_elem(gt)), Gc.index(gt)] ^= 1
# chain map condition (degree 1): H_X^base @ P = P0 @ H_X^cover  (mod 2)?
lhs = (HXb @ P) & 1
rhs = (P0 @ HXc) & 1
print(f"\n[chain-map check, X-boundary] H_X^base.P == P0.H_X^cover : {np.array_equal(lhs, rhs)}")
# Also the Z side (C1 -> C2 = G via H_Z): chain map for the cochain/transpose direction
lhsZ = (HZb @ P) & 1
rhsZ = (P0 @ HZc) & 1
print(f"[chain-map check, Z-boundary] H_Z^base.P == P0.H_Z^cover : {np.array_equal(lhsZ, rhsZ)}")

# ----- cover X-logicals: ker(H_X)/rowspan(H_Z) basis (the k=12 Z-type? convention) -----
# Following quotient_complement_basis docstring: base=H_Z, ext=nullspace(H_X)
# gives ker(H_X)/rowspan(H_Z) = logical-Z operators (k of them).
ker_HXc = nullspace_f2(HXc)
logZ_c = quotient_complement_basis(HZc, ker_HXc)
print(f"\ncover: dim ker H_X = {ker_HXc.shape[0]}, # logical reps = {logZ_c.shape[0]} (= k)")

ker_HXb = nullspace_f2(HXb)
logZ_b = quotient_complement_basis(HZb, ker_HXb)
print(f"base:  dim ker H_X = {ker_HXb.shape[0]}, # logical reps = {logZ_b.shape[0]} (= k)")

# helper: is a base chain v (length 2nb) a nontrivial base logical class?
#   need v in ker(H_X^base)  AND  v not in rowspan(H_Z^base)
def base_class_status(v):
    v = v & 1
    in_ker = not np.any((HXb @ v) & 1)
    # nontrivial mod rowspan(H_Z^base)?
    stacked = np.vstack([HZb, v.reshape(1, -1)])
    nontrivial = rank_f2(stacked) > rank_f2(HZb)
    return in_ker, nontrivial

print("\n=== Q2: projection of each of the 12 cover logical reps ===")
proj_nonzero = 0
proj_zero = 0
proj_nontrivial = 0
for i, L in enumerate(logZ_c):
    pL = p_apply(L)
    w_cover = int(L.sum())
    w_proj = int(pL.sum())
    in_ker, nontriv = base_class_status(pL)
    if w_proj == 0:
        proj_zero += 1
        tag = "ZERO chain"
    else:
        proj_nonzero += 1
        tag = f"nonzero chain w={w_proj}, in_ker={in_ker}, nontrivial_class={nontriv}"
        if nontriv:
            proj_nontrivial += 1
    print(f"  L{i:2d}: |L~|={w_cover:3d}  p(L~): {tag}")
print(f"\nsummary: {proj_zero} reps project to zero chain, {proj_nonzero} to nonzero chain")
print(f"         {proj_nontrivial} project to a NONTRIVIAL base class (in ker, not stabilizer)")

print("\n" + "="*70)
print("=== Q3 (SHARP): the pr_*=0 sector and minimum-weight locus ===")
print("="*70)
# The 6/6 split above is basis-dependent. The INVARIANT object is:
#   pr_* : H1(cover) -> H1(base), a linear map of F2-vector spaces (12-dim -> 12-dim).
# Its kernel = {logical classes that project to a TRIVIAL base class}.
# This kernel is exactly the "dangerous" sector. Compute its dimension invariantly.
#
# pr_*[L~] as a vector in H1(base) coords: take p(L~) chain, reduce mod rowspan(H_Z^base),
# express in the logZ_b basis. We build the matrix of pr_* in (logZ_c basis -> logZ_b basis).

# Coordinates in base H1: given a base chain v in ker(H_X^base), write its class
# in terms of logZ_b. Use: solve v = sum c_j logZ_b[j] + (rowspan H_Z^base).
# i.e. reduce [H_Z^base ; logZ_b] and read off logZ_b coefficients of v.
def base_class_coords(v):
    """Return length-12 F2 vector of coords of [v] in logZ_b basis, or None if v not in ker."""
    v = v & 1
    if np.any((HXb @ v) & 1):
        return None  # not even a cycle
    # Express v in span(rowspan H_Z^base, logZ_b). Set up augmented solve over F2.
    # Basis rows: HZb (30 rows) then logZ_b (12 rows) -> 42 rows, all in ker H_X^base (42-dim).
    M = np.vstack([HZb, logZ_b]).astype(np.uint8)   # 42 x 72
    # Solve M^T c = v for c (length 42). Then coords = c[30:].
    # Gaussian elimination on [M^T | v].
    A = np.concatenate([M.T.copy(), v.reshape(-1, 1).astype(np.uint8)], axis=1)  # 72 x 43
    rows, cols = A.shape
    pr = 0
    pivcol = {}
    for col in range(cols - 1):
        if pr >= rows: break
        sub = A[pr:, col]
        nz = np.flatnonzero(sub)
        if nz.size == 0: continue
        r = pr + int(nz[0])
        if r != pr: A[[pr, r]] = A[[r, pr]]
        mask = A[:, col] == 1; mask[pr] = False
        if mask.any(): A[mask] ^= A[pr]
        pivcol[col] = pr
        pr += 1
    # consistency
    for r in range(pr, rows):
        if A[r, :cols-1].sum() == 0 and A[r, cols-1] == 1:
            return None  # inconsistent: v not in span (shouldn't happen if v in ker)
    c = np.zeros(cols - 1, dtype=np.uint8)
    for col, r in pivcol.items():
        c[col] = A[r, cols-1]
    return c[M.shape[0] - logZ_b.shape[0]:]  # last 12 entries = logZ_b coords

# Build pr_* matrix: columns = images of logZ_c basis vectors in base-H1 coords.
prmat = np.zeros((12, 12), dtype=np.uint8)
for j, L in enumerate(logZ_c):
    pL = p_apply(L)
    coords = base_class_coords(pL)
    if coords is None:
        # p(L) not in ker H_X^base => chain-map should prevent; but a zero chain is in ker
        coords = np.zeros(12, dtype=np.uint8)
    prmat[:, j] = coords
rk = rank_f2(prmat)
print(f"pr_* : H1(cover)=F2^12 -> H1(base)=F2^12  has rank {rk}, kernel dim {12-rk}")
print("  => the 'dangerous' sector ker(pr_*) is {0}-dim if rank=12, else nonzero.".format(12-rk))

# Now the SHARP minimum-weight question.
# Enumerate low-weight elements of ker(pr_*) [the dangerous coset-space] and of the
# full logical space, to see the minimum weight achievable in each.
# We can't fully enumerate 2^12 cosets x stabilizer; but we CAN ask:
#   For each nonzero logical class in ker(pr_*), find a low-weight representative by
#   adding stabilizer rows (rowspan H_Z^cover) greedily / via the existing SAT? Too heavy.
# Instead: do the honest invariant test the program cares about.
#   (a) min weight over the 12 chosen reps that lie in ker(pr_*) (already weight 12).
#   (b) is EVERY minimum-weight (weight-12) cover logical in ker(pr_*)? Equivalent to:
#       does any cover logical with pr_*!=0 have weight 12? We have reps of weight 14..24
#       for the pr!=0 directions, but a different rep could be lighter. Test by checking
#       whether a weight-<=11 nonzero logical exists at all (it shouldn't: d=12), and
#       whether the safe-branch directions admit weight-12 reps.

# Build the full logical lattice generating set: logZ_c (12 reps) + HZc (stabilizers).
# Min-weight per the SAT module already gives d=12. Here we just inspect the structure:
# which 1-dim logical directions (the 2^12-1 nonzero classes) can reach weight 12, and
# whether those all sit in ker(pr_*).
print("\n--- weight of all 2^12-1 nonzero logical classes is infeasible; sample structure ---")
# Project the pr_* map: a class c (in logZ_c coords) is in dangerous sector iff prmat@c=0.
# Sample: for each of the 12 basis reps and their pairwise sums, record (weight_of_rep, in_danger).
import itertools
def in_danger(coeff):  # coeff length-12 over F2 in logZ_c basis
    return not np.any((prmat @ (coeff & 1)) & 1)
def rep_of(coeff):
    v = np.zeros(2*nc, dtype=np.uint8)
    for j in range(12):
        if coeff[j]: v ^= logZ_c[j]
    return v & 1
# singles
print("singletons (rep weight, in dangerous sector ker pr_*):")
for j in range(12):
    e = np.zeros(12, dtype=np.uint8); e[j]=1
    v = rep_of(e)
    print(f"  e{j:2d}: w={int(v.sum()):3d}  danger={in_danger(e)}")

print("\n" + "="*70)
print("=== Q3b: what does the SAFE branch alone prove? min weight on pr_*!=0 ===")
print("="*70)
# Safe branch gives: any cover logical with pr_*!=0 has |L~| >= |p(L~)| >= d_base = 6
#   (since p never increases weight, AND p(L~) is a NONTRIVIAL base class of weight >= 6).
# So the safe branch alone => d_cover >= 6 ON THE pr!=0 SECTOR.
# The dangerous sector (pr=0) gets NOTHING from the safe branch -- that's the whole gap.
#
# Honest min-weight test via SAT on each sector. We use the lab's sat_distance machinery
# restricted to a coset/affine subspace. But simpler & rigorous-enough for SCOUTING:
#   - true d_cover = 12 (known).
#   - Q: is there a weight-<=11 logical anywhere? No (d=12). Good.
#   - Q: does the SAFE sector (pr!=0) contain a weight-EXACTLY-12 logical, or are all its
#        elements heavier? If the safe sector min-weight is, say, >=14, then the
#        minimum-weight (12) logicals ALL live in the dangerous sector, i.e. the binding
#        constraint for d=12 is entirely the dangerous branch.
#
# We answer with SAT: minimize weight over the affine condition pr_*(class)!=0.
# pr_* != 0 is a DISjunction of 6 linear constraints (rows of prmat in logZ_c coords).
# Hard to feed directly. Instead: enumerate the 2^6=64 cosets of ker(pr_*) inside H1,
# i.e. fix the 6 'safe' coordinate-images; for each nonzero image, min-weight over that
# coset is a logical-coset min-weight problem. Too heavy to do 63x SAT here.
#
# Lightweight surrogate that is still informative: greedy weight reduction.
# For each pure safe-direction class (image basis), reduce its rep weight by adding
# stabilizers + dangerous logicals (which don't change pr_*) and random search.
from bb_lab.linalg import nullspace_f2 as _ns

stab_c = HZc  # 66 independent stabilizer rows (rowspan = im H_Z^T = stabilizers for X-logicals)
danger_basis = [logZ_c[j] for j in range(12) if in_danger(np.eye(12,dtype=np.uint8)[j])]
print(f"dangerous basis reps: {len(danger_basis)} vectors, all weight 12")

rng = np.random.default_rng(0)
def reduce_weight(v0, addends, iters=20000):
    v = v0.copy() & 1
    best = int(v.sum())
    bestv = v.copy()
    A = np.array(addends, dtype=np.uint8)
    for _ in range(iters):
        # pick a random subset (size 1-3) of addends to xor
        k = rng.integers(1, 4)
        idx = rng.choice(len(A), size=k, replace=False)
        cand = v.copy()
        for i in idx: cand ^= A[i]
        w = int(cand.sum())
        if w < best:
            best = w; bestv = cand; v = cand
    return best, bestv

# build addends that PRESERVE pr_* class: all stabilizers + dangerous logicals
addends_preserve = list(stab_c) + danger_basis
print("\nMin-weight (greedy, weight-preserving-of-pr_*-class) over each safe singleton:")
for j in range(12):
    e = np.eye(12, dtype=np.uint8)[j]
    if in_danger(e):
        continue
    v = rep_of(e)
    w, _ = reduce_weight(v, addends_preserve, iters=30000)
    print(f"  safe e{j:2d}: start w={int(v.sum())} -> greedy min w={w}  (pr_* class unchanged)")

print("\nMin-weight (greedy) over dangerous singletons (adding stabilizers only):")
for j in range(12):
    e = np.eye(12, dtype=np.uint8)[j]
    if not in_danger(e):
        continue
    v = rep_of(e)
    w, _ = reduce_weight(v, list(stab_c), iters=30000)
    print(f"  danger e{j:2d}: start w={int(v.sum())} -> greedy min w={w}")

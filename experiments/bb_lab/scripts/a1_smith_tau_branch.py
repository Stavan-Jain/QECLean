"""Pin the crux: is the dangerous (pr=0) sector covered by tr_* (tau-lift, weight-doubling)
or does it fall into Ker(tr_*) = Im(Delta = cap omega) -- the genuinely hard obstruction?

Smith exactness:  ... -> H1(base) --tr--> H1(cover) --pr--> H1(base) --Delta--> H0...
For a free Z2 cover the relevant exact piece is:
   H2(base) --Delta--> H1(base) --tr--> H1(cover) --pr--> H1(base) --Delta--> H1(base)...
The dangerous sector ker(pr_*) (6-dim, computed) = Im(tr_*) by exactness.
tr_* = lifting tau on homology; tau(x^a y^b) = sum over the 2 fibre lifts = weight DOUBLING
at chain level. So a class in Im(tr_*) has a representative tau(c) for some base cycle c,
of weight 2|c|. If |c| can be as small as d_base/... that bounds the dangerous class weight
from... ABOVE, not below. The LOWER bound needs: every cover rep of a dangerous class is heavy.

Concretely, the question the Smith argument must answer to get d_cover >= 12 on this sector:
   for a dangerous class [L~] = tr_*[c], is min over reps |L~| forced >= 12?
We test the chain-level lifting map tau and whether tau(base logicals) reproduce the
dangerous sector, and compare weights.
"""
from __future__ import annotations
import numpy as np
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, quotient_complement_basis, rank_f2

Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
nc, nb = Gc.cardinality, Gb.cardinality
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z

# lifting tau on C1: tau(base qubit (g',block)) = sum of the 2 cover qubits projecting to it.
# cover g_tilde projects to g' iff g_tilde mod (6,6) = g'. For Z12 x Z6 -> Z6 x Z6: the
# y-axis (order 6 -> 6) lifts trivially (1 preimage), the x-axis (12 -> 6) has 2 preimages
# {a, a+6}. So each base element has exactly 2 lifts. tau matrix T: 2nc x 2nb.
T = np.zeros((2*nc, 2*nb), dtype=np.uint8)
for gt in Gc:
    gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
    T[Gc.index(gt), Gb.index(gb)] = 1
    T[nc+Gc.index(gt), nb+Gb.index(gb)] = 1
# check p . tau = h . I = 2I = 0 over F2 (SRB Lemma 4.4)
P = np.zeros((2*nb, 2*nc), dtype=np.uint8)
for gt in Gc:
    gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
    P[Gb.index(gb), Gc.index(gt)] ^= 1
    P[nb+Gb.index(gb), nc+Gc.index(gt)] ^= 1
PT = (P @ T) & 1
print(f"p . tau = 0 over F2 (SRB Lemma 4.4, h=2 even): {not PT.any()}")

# tau is a chain map base->cover: H_X^cover . tau = tau0 . H_X^base ?
T0 = np.zeros((nc, nb), dtype=np.uint8)
for gt in Gc:
    gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
    T0[Gc.index(gt), Gb.index(gb)] = 1
lhs = (HXc @ T)&1; rhs = (T0 @ HXb)&1
print(f"tau is a chain map (H_X^c . tau == tau0 . H_X^b): {np.array_equal(lhs, rhs)}")

# base logical-Z reps (cycles of H_X^base), lift them, see weights & whether nonzero in cover H1
ker_HXb = nullspace_f2(HXb); logZ_b = quotient_complement_basis(HZb, ker_HXb)
ker_HXc = nullspace_f2(HXc); logZ_c = quotient_complement_basis(HZc, ker_HXc)
ker_HZc = nullspace_f2(HZc); logX_c = quotient_complement_basis(HXc, ker_HZc)

print("\n=== tau-lifts of the 12 base logical-Z reps ===")
nonzero_lift = 0
for j in range(logZ_b.shape[0]):
    c = logZ_b[j] & 1
    tc = (T @ c) & 1
    # is tau(c) a cover cycle? H_Z^c . tau(c) = ? (need tau chain map on Z side too)
    is_cycle = not np.any((HZc @ tc) & 1)
    # nontrivial in cover H1? anticommutes some logX_c
    nontriv = np.any((logX_c @ tc) & 1) if is_cycle else False
    if nontriv: nonzero_lift += 1
    print(f"  base logZ[{j:2d}] |c|={int(c.sum()):2d} -> |tau(c)|={int(tc.sum()):2d}  cover-cycle={is_cycle} nontrivial={nontriv}")
print(f"\n{nonzero_lift}/12 base logicals lift to NONTRIVIAL cover classes via tau")
print("(SRB even-h: H1(tau).H1(p)=0; tau need NOT be injective on H1 -- this is the gap.)")

# Key: dim Im(tr_*) should equal dim ker(pr_*) = 6 (Smith exactness). Verify by building
# the matrix of tr_* = H1(tau): base H1 (12) -> cover H1 (12).
# coords of tau(c) class in logZ_c basis.
def cover_class_coords(v):
    v = v & 1
    if np.any((HXc @ v)&1): return None
    M = np.vstack([HZc, logZ_c]).astype(np.uint8)
    A = np.concatenate([M.T.copy(), v.reshape(-1,1)], axis=1)
    rows, cols = A.shape; pr=0; piv={}
    for col in range(cols-1):
        if pr>=rows: break
        nz = np.flatnonzero(A[pr:,col])
        if nz.size==0: continue
        r=pr+int(nz[0])
        if r!=pr: A[[pr,r]]=A[[r,pr]]
        m=A[:,col]==1; m[pr]=False
        if m.any(): A[m]^=A[pr]
        piv[col]=pr; pr+=1
    c=np.zeros(cols-1,dtype=np.uint8)
    for col,r in piv.items(): c[col]=A[r,cols-1]
    return c[M.shape[0]-logZ_c.shape[0]:]
trmat = np.zeros((12,12),dtype=np.uint8)
for j in range(logZ_b.shape[0]):
    tc = (T @ (logZ_b[j]&1))&1
    co = cover_class_coords(tc)
    if co is not None: trmat[:,j]=co
print(f"\ndim Im(tr_*) = rank(trmat) = {rank_f2(trmat)}  (Smith: should match ker(pr_*) dim = 6)")

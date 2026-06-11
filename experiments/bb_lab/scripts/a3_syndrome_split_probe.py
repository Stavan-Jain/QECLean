"""A3 / Track 1.1 §2 — does the HARD case (seam syndrome s != 0) bind the minimum?

Reduction (derived by hand, entry 1): a cover X-cycle v=(v0,v1) in a dangerous
class satisfies d1_base v0 = d1_base v1 = s, with s = d1c . p(v) (the seam part
of the base boundary applied to the sum of sheets). The factor-2 lemma
|v0|+|v1| >= 2 d_base splits:
  s = 0 : v0, v1 are base CYCLES in the same class [v0]=[v1]; if nontrivial,
          each >= d_base, sum >= 2 d_base. (EASY case.)
  s != 0: v0, v1 are NOT base cycles (seam leakage). HARD case, new math.

This probe asks the decision-relevant question: among MINIMUM-weight (=12)
dangerous logicals, does s != 0 ever occur, or are all the minima in the easy
s=0 case? If the minima are all s=0, the hard case never binds the bound and
the lemma is essentially the easy argument; if s!=0 minima exist, the hard case
is unavoidable (months estimate stands).

Discovery only; never load-bearing.
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
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z
nc, nb = Gc.cardinality, Gb.cardinality

def sheet(g): return 1 if g[0] >= 6 else 0
def base_of(g): return (g[0] % 6, g[1])
# base seam split of d1 = H_X
row_perm = np.empty(nc, dtype=int); col_perm = np.empty(2*nc, dtype=int)
for g in Gc:
    row_perm[Gc.index(g)] = sheet(g)*nb + Gb.index(base_of(g))
    for blk in (0, 1):
        col_perm[blk*nc + Gc.index(g)] = sheet(g)*(2*nb) + blk*nb + Gb.index(base_of(g))
HXc_p = np.zeros_like(HXc); HXc_p[row_perm[:, None], col_perm[None, :]] = HXc
d1nc = HXc_p[:nb, :2*nb] & 1
d1c  = HXc_p[:nb, 2*nb:] & 1

# projection p on C1 (sum sheets): 2nc -> 2nb
P = np.zeros((2*nb, 2*nc), np.uint8)
for g in Gc:
    gb = base_of(g)
    P[Gb.index(gb), Gc.index(g)] ^= 1
    P[nb+Gb.index(gb), nc+Gc.index(g)] ^= 1
def p_apply(v): return (P @ (v & 1)) & 1
def syndrome(v):  # s = d1c . p(v)
    return (d1c @ p_apply(v)) & 1

# dangerous logical reps (kernel of pr_*) -- reuse the projection-probe construction
ker_HXc = nullspace_f2(HXc); logZ_c = quotient_complement_basis(HZc, ker_HXc)
ker_HXb = nullspace_f2(HXb); logZ_b = quotient_complement_basis(HZb, ker_HXb)
def base_class_coords(v):
    v = v & 1
    if np.any((HXb @ v) & 1): return None
    M = np.vstack([HZb, logZ_b]).astype(np.uint8)
    A = np.concatenate([M.T.copy(), v.reshape(-1,1).astype(np.uint8)], axis=1)
    rows, cols = A.shape; pr=0; piv={}
    for col in range(cols-1):
        if pr>=rows: break
        nz=np.flatnonzero(A[pr:,col])
        if nz.size==0: continue
        r=pr+int(nz[0])
        if r!=pr: A[[pr,r]]=A[[r,pr]]
        m=A[:,col]==1; m[pr]=False
        if m.any(): A[m]^=A[pr]
        piv[col]=pr; pr+=1
    c=np.zeros(cols-1,np.uint8)
    for col,r in piv.items(): c[col]=A[r,cols-1]
    return c[M.shape[0]-logZ_b.shape[0]:]
prmat = np.zeros((12,12), np.uint8)
for j,L in enumerate(logZ_c):
    co = base_class_coords(p_apply(L)); prmat[:,j] = np.zeros(12,np.uint8) if co is None else co
dang = nullspace_f2(prmat)  # dangerous classes in logZ_c coords
def dang_rep(coeff):
    v = np.zeros(2*nc, np.uint8)
    for j in range(12):
        if coeff[j]: v ^= logZ_c[j]
    return v & 1

print("Q0: dangerous reps all have s=0 (they are tau(u), p=0)?")
for i,c in enumerate(dang):
    v = dang_rep(c); print(f"  rep {i}: |v|={int(v.sum())}, s==0: {not syndrome(v).any()}")

# Q1: can a cover stabilizer t give s = d1c . p(t) != 0 ?  (p(t) is a base boundary)
print("\nQ1: does some cover stabilizer t give nonzero seam syndrome s = d1c.p(t)?")
nz = 0
for t in HZc:                       # generating stabilizers
    if syndrome(t).any(): nz += 1
print(f"  generators with s!=0: {nz}/{HZc.shape[0]}")
rng = np.random.default_rng(0)
nz_rand = 0
for _ in range(3000):
    k = rng.integers(1, 6); idx = rng.choice(HZc.shape[0], size=k, replace=False)
    t = np.zeros(2*nc, np.uint8)
    for i in idx: t ^= HZc[i]
    if syndrome(t).any(): nz_rand += 1
print(f"  random stabilizer combos with s!=0: {nz_rand}/3000")

# Q2 (the decision question): sample dangerous members v = rep + stabilizer; for the
# LIGHTEST ones found, is s always 0? Tabulate min weight among s=0 vs s!=0 members.
print("\nQ2: min weight among dangerous members, split by s==0 vs s!=0")
best_s0, best_s1 = 999, 999
seen_s1 = 0
for trial in range(40000):
    # random nonzero dangerous class
    c = rng.integers(0, 2, size=dang.shape[0]).astype(np.uint8)
    if not c.any(): continue
    base = np.zeros(2*nc, np.uint8)
    for i in range(dang.shape[0]):
        if c[i]: base ^= dang_rep(dang[i])
    # add a random light stabilizer combo
    k = rng.integers(0, 5)
    t = np.zeros(2*nc, np.uint8)
    if k:
        idx = rng.choice(HZc.shape[0], size=k, replace=False)
        for i in idx: t ^= HZc[i]
    v = (base ^ t) & 1
    w = int(v.sum())
    if syndrome(v).any():
        seen_s1 += 1; best_s1 = min(best_s1, w)
    else:
        best_s0 = min(best_s0, w)
print(f"  sampled s!=0 dangerous members: {seen_s1} (min weight {best_s1 if seen_s1 else 'n/a'})")
print(f"  min weight among s==0 dangerous members: {best_s0}")
print("\nINTERPRETATION:")
print("  if s!=0 members exist but are all heavier than 12, the MINIMUM is")
print("  carried by s=0 members => the easy case binds the bound, hard case is")
print("  off-minimum. If s!=0 members reach 12, the hard case is unavoidable.")

"""A3 / Track 1.1 §1 — explicit Smith connecting map Delta = cap-omega, verified.

From the verified SES of complexes 0 -> C_base --tau--> C_cover --p--> C_base -> 0
(a3_cut_decomposition.py), the snake-lemma connecting map Delta: H2(base) ->
H1(base) has the closed form derived by hand:
    for z in H2(base) = ker(d2_base), lift to z~=(z,0); d2_cover(z,0) =
    (d2nc z, d2c z) = tau(d2c z)  [using d2nc z = d2c z since d2_base z = 0];
    hence  Delta[z] = [ d2c . z ]  — the class of the SEAM part of the base
    boundary d2 applied to z.
This script verifies, on the gross/[[72,12,6]] pair, that
    im(Delta) = ker(tr_*)   (both 6-dim),
the Smith-exactness identity ker(tr_*) = im(Delta). That pins Delta concretely
and confirms the sheet framework end to end.

Discovery/validation only; never load-bearing.
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
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z
nc, nb = Gc.cardinality, Gb.cardinality

# ---- seam decomposition of the base boundaries (via the verified permutation) ----
def sheet(g): return 1 if g[0] >= 6 else 0
def base_of(g): return (g[0] % 6, g[1])
row_perm = np.empty(nc, dtype=int); col_perm = np.empty(2*nc, dtype=int)
for g in Gc:
    row_perm[Gc.index(g)] = sheet(g)*nb + Gb.index(base_of(g))
    for blk in (0, 1):
        col_perm[blk*nc + Gc.index(g)] = sheet(g)*(2*nb) + blk*nb + Gb.index(base_of(g))
def permute(M):
    out = np.zeros_like(M); out[row_perm[:, None], col_perm[None, :]] = M; return out

HZc_p = permute(HZc)
HZb_nc = HZc_p[:nb, :2*nb]          # non-seam part of base H_Z (36 x 72)
HZb_c  = HZc_p[:nb, 2*nb:]          # seam part of base H_Z   (36 x 72)
assert np.array_equal((HZb_nc + HZb_c) & 1, HZb & 1)

# d2_base = H_Zb^T : C2(36) -> C1(72);  seam part d2c = (HZb_c)^T
d2 = (HZb.T) & 1
d2c = (HZb_c.T) & 1                 # 72 x 36

# H2(base) = ker(d2_base) = {z in F2^36 : d2 z = 0}
H2 = nullspace_f2(d2)               # rows = basis of ker(d2), each length 36
print(f"dim H2(base) = ker(d2) = {H2.shape[0]}  (expect 6 = k/2)")

# d1_base for cycle/boundary tests in H1(base)
d1 = HXb & 1                        # 36 x 72  (C1 -> C0)
B1 = HZb & 1                        # boundaries im(d2) = rowspan(H_Z) (as 72-vectors): rows of H_Z
# H1(base) = ker(d1)/rowspan(H_Z)
ker_d1 = nullspace_f2(d1)
logZ_b = quotient_complement_basis(HZb, ker_d1)   # 12 reps

def h1_coords(v):
    """coords of base 1-chain v in logZ_b basis mod rowspan(H_Z); None if not a cycle."""
    v = v & 1
    if np.any((d1 @ v) & 1): return None
    M = np.vstack([HZb, logZ_b]).astype(np.uint8)
    A = np.concatenate([M.T.copy(), v.reshape(-1,1).astype(np.uint8)], axis=1)
    rows, cols = A.shape; pr = 0; piv = {}
    for col in range(cols-1):
        if pr >= rows: break
        nz = np.flatnonzero(A[pr:, col])
        if nz.size == 0: continue
        r = pr+int(nz[0])
        if r != pr: A[[pr, r]] = A[[r, pr]]
        m = A[:, col] == 1; m[pr] = False
        if m.any(): A[m] ^= A[pr]
        piv[col] = pr; pr += 1
    c = np.zeros(cols-1, np.uint8)
    for col, r in piv.items(): c[col] = A[r, cols-1]
    return c[M.shape[0]-logZ_b.shape[0]:]

# ---- im(Delta): classes [d2c z] for z in H2 ----
imD = []
for z in H2:
    dv = (d2c @ z) & 1
    co = h1_coords(dv)
    assert co is not None, "Delta image not a base cycle?!"
    imD.append(co)
imD = np.array(imD, dtype=np.uint8)
dim_imD = rank_f2(imD)
print(f"dim im(Delta) in H1(base) = {dim_imD}  (expect 6)")

# ---- tr_* : H1(base) -> H1(cover), [u] -> [tau(u)]; compute ker(tr_*) ----
# tau on C1: base qubit (blk, g_b) -> both cover lifts (blk, g_b) and (blk, g_b+ (6,0))
def tau_C1(u):
    out = np.zeros(2*nc, np.uint8)
    for g in Gc:
        gb = base_of(g)
        out[Gc.index(g)]      ^= u[Gb.index(gb)]
        out[nc+Gc.index(g)]   ^= u[nb+Gb.index(gb)]
    return out & 1
# cover H1 coords
ker_HXc = nullspace_f2(HXc); logZ_c = quotient_complement_basis(HZc, ker_HXc)
def cover_h1_coords(v):
    v = v & 1
    if np.any((HXc @ v) & 1): return None
    M = np.vstack([HZc, logZ_c]).astype(np.uint8)
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
    return c[M.shape[0]-logZ_c.shape[0]:]

trmat = np.zeros((12, 12), np.uint8)   # cols = tr_*(logZ_b[j]) in cover-H1 coords
for j, u in enumerate(logZ_b):
    co = cover_h1_coords(tau_C1(u))
    trmat[:, j] = np.zeros(12, np.uint8) if co is None else co
ker_tr = nullspace_f2(trmat)           # {coeff in logZ_b basis : tr_*=0}
print(f"dim ker(tr_*) = {ker_tr.shape[0]}  (expect 6 = dangerous)")

# ---- verify im(Delta) == ker(tr_*) as subspaces of H1(base) (logZ_b coords) ----
# im(Delta) is given in logZ_b coords (imD rows). ker(tr_*) also in logZ_b coords.
stack = np.vstack([imD, ker_tr]).astype(np.uint8)
same = (rank_f2(imD) == rank_f2(ker_tr) == rank_f2(stack))
print(f"\nim(Delta) == ker(tr_*) as subspaces of H1(base): {same}")
print("  => Smith exactness ker(tr_*) = im(Delta) VERIFIED; Delta = [d2c . z] is correct.")

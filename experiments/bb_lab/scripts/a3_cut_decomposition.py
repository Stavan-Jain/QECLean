"""A3 / Track 1.1 §1 — verify the sheet/cut structure of the cover boundary.

The whole sheet framework rests on the claim that, in sheet coordinates
(sheet 0 = {x<6}, sheet 1 = {x>=6}, deck sigma: x -> x+6), the cover boundary
maps have the 2x2 block form
        [[ d_nc , d_c ],
         [ d_c , d_nc ]]
with d_nc + d_c = the BASE boundary, d_c = the x-seam-crossing part. This script
PROVES that for both H_X (d_1) and H_Z^T (d_2) by permuting the lab-built cover
matrices into (sheet, base) order and checking the structure exactly.

If verified, d_1nc/d_1c (and d_2nc/d_2c) are the explicit ingredients of the
cut cocycle omega and the Smith connecting map Delta = cap-omega.

Discovery/validation only; never load-bearing in a final proof.
"""
from __future__ import annotations
import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices

Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z
nc, nb = Gc.cardinality, Gb.cardinality   # 72, 36

def sheet(gt):       # cover element -> 0/1
    return 1 if gt[0] >= 6 else 0
def base_of(gt):     # cover element -> base element
    return (gt[0] % 6, gt[1])

# ---- permutations: cover check-row index -> (sheet, base_check_index) ----
# H_X rows indexed by g in Gc (|G| rows); H_X cols indexed by (block, g): col = block*nc + Gc.index(g)
row_perm = np.empty(nc, dtype=int)        # new position of cover row Gc.index(g)
for g in Gc:
    row_perm[Gc.index(g)] = sheet(g) * nb + Gb.index(base_of(g))
col_perm = np.empty(2*nc, dtype=int)      # new position of cover col block*nc+Gc.index(g)
for g in Gc:
    for blk in (0, 1):
        old = blk * nc + Gc.index(g)
        # new order: (sheet, block, base) -> sheet*72 + block*36 + base_index
        col_perm[old] = sheet(g) * (2*nb) + blk * nb + Gb.index(base_of(g))

def permute(M, rp, cp):
    out = np.zeros_like(M)
    out[rp[:, None], cp[None, :]] = M
    return out

HXc_p = permute(HXc, row_perm, col_perm)   # 72 x 144, in (sheet,base)x(sheet,block,base) order
# split into 2x2 sheet blocks; each block is 36 x 72 (base-checks x base-qubits = base H_X shape)
B00 = HXc_p[:nb, :2*nb]
B01 = HXc_p[:nb, 2*nb:]
B10 = HXc_p[nb:, :2*nb]
B11 = HXc_p[nb:, 2*nb:]

print("=== H_X (d_1) sheet structure ===")
print(f"  B00 == B11 (d_nc equal on both sheets): {np.array_equal(B00, B11)}")
print(f"  B01 == B10 (d_c equal off-diagonal):    {np.array_equal(B01, B10)}")
print(f"  B00 + B01 == base H_X:                   {np.array_equal((B00 + B01) & 1, HXb & 1)}")
d1nc, d1c = B00, B01
print(f"  |support d_1nc| = {int(d1nc.sum())}, |support d_1c| = {int(d1c.sum())}  (d_c = seam part)")
print(f"  d_1c nonzero (seam genuinely crosses): {bool(d1c.any())}")

# ---- same for H_Z (d_2 = H_Z^T) ----
# H_Z rows indexed by g (Z-checks), cols by (block,g). Use same perms (transpose handled by shape).
HZc_p = permute(HZc, row_perm, col_perm)
Z00 = HZc_p[:nb, :2*nb]; Z01 = HZc_p[:nb, 2*nb:]; Z10 = HZc_p[nb:, :2*nb]; Z11 = HZc_p[nb:, 2*nb:]
print("\n=== H_Z sheet structure ===")
print(f"  Z00 == Z11: {np.array_equal(Z00, Z11)}")
print(f"  Z01 == Z10: {np.array_equal(Z01, Z10)}")
print(f"  Z00 + Z01 == base H_Z: {np.array_equal((Z00 + Z01) & 1, HZb & 1)}")
print(f"  |support Z_nc| = {int(Z00.sum())}, |support Z_c| = {int(Z01.sum())}")

# ---- which base monomials cross the seam? (sanity: only x^a with a>0) ----
# d_1c is the part of base H_X = [A|B] whose x-shift carried past 6.
print("\n=== seam-crossing monomials (expected: x^3 in A; x, x^2 in B) ===")
# A-block (first nb cols of base H_X) seam part, B-block (last nb cols)
A_seam = d1c[:, :nb]; B_seam = d1c[:, nb:]
print(f"  A-block has seam-crossing entries: {bool(A_seam.any())}  (A has x^3)")
print(f"  B-block has seam-crossing entries: {bool(B_seam.any())}  (B has x, x^2)")

verified = (np.array_equal(B00, B11) and np.array_equal(B01, B10)
            and np.array_equal((B00 + B01) & 1, HXb & 1)
            and np.array_equal(Z00, Z11) and np.array_equal(Z01, Z10)
            and np.array_equal((Z00 + Z01) & 1, HZb & 1))
print(f"\nSHEET/CUT STRUCTURE VERIFIED for both boundaries: {verified}")

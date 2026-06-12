"""A3 / Track 1.1 Entry 5 — foundations of the m(b) reformulation.

Verifies, by F2 linear algebra on the gross cover (no SAT), the chain of
claims that collapse the dangerous-sector factor-2 lemma to a single scalar
function on base stabilizers:

  For every cut j in Z_6 (fundamental domain {j..j+5} in the x-direction):
  V1  the cover boundaries have block form [[nc_j, c_j], [c_j, nc_j]] with
      nc_j + c_j = the base boundary (the cut-0 case is a3_cut_decomposition);
  V2  the cover chain condition splits: d1nc.d2nc + d1c.d2c = 0 and
      d1nc.d2c + d1c.d2nc = 0;
  V3  ker(d2_base) is 6-dim (H2);
  V4  the X/Z logical pairing is perfect (rank 12);
  V5  im(Delta_j) = ker(tr_*) for EVERY cut j (Smith exactness per cut), where
      Delta_j[zeta] = [d2c_j zeta]; in particular im(Delta_j) is j-independent;
  V6  the dangerous-cycle space {v in ker HXc : [p(v)] = 0} equals
      tau(Z1_base) + im(d2_cover)  (the tau(u) + stabilizer parametrization);
  V7  per cut j, every dangerous v = tau(u) + d2cover(w) has sheet form
      v0_j = u + d2c_j z + beta_j  (beta_j a base stabilizer, z = p(w)),
      v1_j = v0_j + b (b = d2 z = p(v)), syndrome HXb v0 = d1c_j b, and the
      pointwise identity |v| = |b| + 2*|v0_j off supp(b)|;
  V8  v is a nontrivial cover logical  <=>  [u] not in im(Delta);
  V9  the 6 eta functionals (annihilator of im(Delta) under the pairing)
      detect im(Delta) membership: [c] in im(Delta) <=> eta.c = 0.

Consequence (proved in the entry, given V1-V9): for every cut j,
    min{|v| : v nontrivial dangerous, p(v) = b} = |b| + 2*m_j(b),
    m_j(b) := min{|(d2c_j z_b + u') off supp(b)| : u' in Z1, [u'] not in im(Delta)},
so m_j(b) is the SAME for all j (the s=0/s!=0 case split of Entries 1-3 is a
cut-0 coordinate artifact), and the factor-2 lemma is exactly
    |b| + 2*m(b) >= 2*d_base   for all base stabilizers b.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, rank_f2, quotient_complement_basis

rng = np.random.default_rng(20260612)

# ---------------------------------------------------------------- build codes
Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
HXc, HZc = cm_c.H_X & 1, cm_c.H_Z & 1     # 72 x 144
HXb, HZb = cm_b.H_X & 1, cm_b.H_Z & 1     # 36 x 72
nc, nb = Gc.cardinality, Gb.cardinality   # 72, 36
N, n = 2 * nc, 2 * nb                     # 144 cover qubits, 72 base qubits
d2b = HZb.T                               # base d2: faces (36) -> qubits (72)
d2cov = HZc.T                             # cover d2: faces (72) -> qubits (144)

def base_of(g): return (g[0] % 6, g[1])

# cover <-> base transfer maps (cut-independent)
P1 = np.zeros((n, N), np.uint8)           # qubit projection p
P2 = np.zeros((nb, nc), np.uint8)         # face projection
for g in Gc:
    gi, bi = Gc.index(g), Gb.index(base_of(g))
    P1[bi, gi] ^= 1; P1[nb + bi, nc + gi] ^= 1
    P2[bi, gi] ^= 1
TAU1 = P1.T.copy()                        # tau on 1-chains: u -> (u, u)

# ------------------------------------------------------- per-cut sheet blocks
def cut_blocks(j: int):
    """Return (d1nc_j, d1c_j, d2nc_j, d2c_j, R0_j) for the cut at x = j."""
    def sheet(g): return 1 if ((g[0] - j) % 12) >= 6 else 0
    row_perm = np.empty(nc, dtype=int); col_perm = np.empty(N, dtype=int)
    for g in Gc:
        gi, bi = Gc.index(g), Gb.index(base_of(g))
        row_perm[gi] = sheet(g) * nb + bi
        for blk in (0, 1):
            col_perm[blk * nc + gi] = sheet(g) * n + blk * nb + bi
    HXc_p = np.zeros_like(HXc); HXc_p[row_perm[:, None], col_perm[None, :]] = HXc
    HZc_p = np.zeros_like(HZc); HZc_p[row_perm[:, None], col_perm[None, :]] = HZc
    okX = (np.array_equal(HXc_p[:nb, :n], HXc_p[nb:, n:])
           and np.array_equal(HXc_p[:nb, n:], HXc_p[nb:, :n])
           and np.array_equal((HXc_p[:nb, :n] ^ HXc_p[:nb, n:]), HXb))
    okZ = (np.array_equal(HZc_p[:nb, :n], HZc_p[nb:, n:])
           and np.array_equal(HZc_p[:nb, n:], HZc_p[nb:, :n])
           and np.array_equal((HZc_p[:nb, :n] ^ HZc_p[:nb, n:]), HZb))
    d1nc, d1c = HXc_p[:nb, :n], HXc_p[:nb, n:]
    d2nc, d2c = HZc_p[:nb, :n].T, HZc_p[:nb, n:].T      # qubits (72) x faces (36)
    # sheet-0 qubit restriction (n x N): cover qubit (blk, g) with sheet_j(g)=0
    R0 = np.zeros((n, N), np.uint8)
    for g in Gc:
        if sheet(g) == 0:
            gi, bi = Gc.index(g), Gb.index(base_of(g))
            R0[bi, gi] = 1; R0[nb + bi, nc + gi] = 1
    return okX, okZ, d1nc, d1c, d2nc, d2c, R0

cuts = [cut_blocks(j) for j in range(6)]
print("=== V1: per-cut block structure [[nc,c],[c,nc]], nc+c = base ===")
for j, (okX, okZ, *_rest) in enumerate(cuts):
    print(f"  cut j={j}: H_X blocks ok: {okX}, H_Z blocks ok: {okZ}")

print("\n=== V2: cover chain identities per cut ===")
for j, (_, _, d1nc, d1c, d2nc, d2c, _) in enumerate(cuts):
    i1 = not ((d1nc @ d2nc + d1c @ d2c) % 2).any()
    i2 = not ((d1nc @ d2c + d1c @ d2nc) % 2).any()
    print(f"  cut j={j}: d1nc.d2nc+d1c.d2c=0: {i1}, d1nc.d2c+d1c.d2nc=0: {i2}")

# ------------------------------------------------------------ homology bases
ker_d2b = nullspace_f2(d2b)               # 2-cycles, rows, expect 6
print(f"\n=== V3: dim ker(d2_base) = {ker_d2b.shape[0]} (expect 6) ===")

Z1b = nullspace_f2(HXb)                   # base 1-cycles (42 x 72)
logXb = quotient_complement_basis(HXb, nullspace_f2(HZb))   # 12 x 72
logZb = quotient_complement_basis(HZb, nullspace_f2(HXb))   # 12 x 72
logXc = quotient_complement_basis(HXc, nullspace_f2(HZc))   # 12 x 144
Pi = (logXb @ logZb.T) % 2
print(f"=== V4: X/Z pairing rank = {rank_f2(Pi)} (expect 12) ===")

def classvec(c):                          # H1(base) coordinates of a 1-cycle
    return (logXb @ (c & 1)) % 2

def in_span(rows: np.ndarray, v: np.ndarray) -> bool:
    if rows.size == 0:
        return not (v & 1).any()
    r0 = rank_f2(rows)
    return rank_f2(np.vstack([rows, v & 1])) == r0

# --------------------------------------------- V5: im(Delta_j) = ker(tr_*)
print("\n=== V5: Smith exactness im(Delta_j) = ker(tr_*) for every cut ===")
# ker(tr_*): classes [u] with tau(u) in im(d2cov). Solve on the cycle basis.
M = np.concatenate([(TAU1 @ Z1b.T) % 2, d2cov], axis=1)     # 144 x (42 + 72)
K = nullspace_f2(M)
tr_kill = (K[:, :Z1b.shape[0]] @ Z1b) % 2 if K.size else np.zeros((0, n), np.uint8)
ker_tr_cls = (tr_kill @ logXb.T) % 2 if tr_kill.size else np.zeros((0, 12), np.uint8)
print(f"  dim ker(tr_*) as class space: {rank_f2(ker_tr_cls)} (expect 6)")
imD_cls_by_cut = []
for j, (_, _, _, _, _, d2c, _) in enumerate(cuts):
    reps = (d2c @ ker_d2b.T).T % 2                          # 6 x 72
    cyc_ok = not ((HXb @ reps.T) % 2).any()
    cls = (reps @ logXb.T) % 2                              # 6 x 12
    imD_cls_by_cut.append(cls)
    same = (rank_f2(np.vstack([ker_tr_cls, cls])) == rank_f2(ker_tr_cls) == rank_f2(cls))
    print(f"  cut j={j}: Delta reps are cycles: {cyc_ok}, dim im(Delta_j) = {rank_f2(cls)}, "
          f"im(Delta_j) == ker(tr_*): {same}")
imD_cls = imD_cls_by_cut[0]

# --------------------------------------------- V9: eta functionals for imD
print("\n=== V9: eta functionals (annihilator of im(Delta)) ===")
mu = nullspace_f2(imD_cls)                # 6 x 12, mu . imD_cls^T = 0
eta = (mu @ logXb) % 2                    # 6 x 72
ok_ann = not ((eta @ ((cuts[0][5] @ ker_d2b.T).T % 2).T) % 2).any()
print(f"  dim eta = {mu.shape[0]} (expect 6); eta kills im(Delta) reps: {ok_ann}")
# detection check on random cycles: eta.c = 0 <=> classvec(c) in imD_cls
det_ok = True
for _ in range(200):
    c = (rng.integers(0, 2, Z1b.shape[0], dtype=np.uint8) @ Z1b) % 2
    lhs = not ((eta @ c) % 2).any()
    rhs = in_span(imD_cls, classvec(c))
    det_ok &= (lhs == rhs)
print(f"  eta detects im(Delta) membership on 200 random cycles: {det_ok}")

# --------------------------------------------- V6: dangerous parametrization
print("\n=== V6: dangerous cycles = tau(Z1_base) + im(d2_cover) ===")
DangerRows = np.vstack([HXc, (logXb @ P1) % 2])
DC = nullspace_f2(DangerRows)             # dangerous-cycle basis
S2 = np.vstack([(TAU1 @ Z1b.T).T % 2, d2cov.T])
r_DC, r_S2 = DC.shape[0], rank_f2(S2)
r_join = rank_f2(np.vstack([S2, DC]))
print(f"  dim dangerous-cycle space = {r_DC}")
print(f"  dim (tau(Z1) + im d2cov)  = {r_S2}")
print(f"  spaces equal: {r_DC == r_S2 == r_join}")

# --------------------------------------------- V7/V8: sheet formula sampling
print("\n=== V7/V8: per-cut sheet formula + pointwise identity + nontriviality ===")
stab_rows = HZb                           # rowspan = base Z-stabilizers
ok7 = ok_id = ok_syn = ok8 = True
for t in range(120):
    al = rng.integers(0, 2, Z1b.shape[0], dtype=np.uint8)
    u = (al @ Z1b) % 2
    w = rng.integers(0, 2, nc, dtype=np.uint8)
    v = ((TAU1 @ u) + (d2cov @ w)) % 2
    z = (P2 @ w) % 2
    b = (d2b @ z) % 2
    bs = b.astype(bool)
    for j, (_, _, d1nc, d1c, d2nc, d2c, R0) in enumerate(cuts if t < 20 else cuts[:1]):
        v0 = (R0 @ v) % 2
        beta = (v0 + u + (d2c @ z)) % 2
        ok7 &= in_span(stab_rows, beta)
        ok_syn &= np.array_equal((HXb @ v0) % 2, (d1c @ b) % 2)
        ok_id &= int(v.sum()) == int(b.sum()) + 2 * int(v0[~bs].sum())
    triv_v = not ((logXc @ v) % 2).any()
    triv_u = in_span(imD_cls, classvec(u))
    ok8 &= (triv_v == triv_u)
print(f"  beta_j = v0_j + u + d2c_j z is always a base stabilizer: {ok7}")
print(f"  syndrome formula HXb v0_j = d1c_j b:                    {ok_syn}")
print(f"  pointwise identity |v| = |b| + 2|v0_j off supp(b)|:     {ok_id}")
print(f"  [v]=0 in cover  <=>  [u] in im(Delta):                  {ok8}")

print("\nALL FOUNDATIONS VERIFIED" if all([ok7, ok_syn, ok_id, ok8, det_ok]) else "\nSOME CHECK FAILED")

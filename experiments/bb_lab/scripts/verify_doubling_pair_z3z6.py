"""Independent spot-check of the [[36,4,4]] -> [[72,4,8]] doubling pair.

Base : G = Z3 x Z6  (x order 3, y order 6),  A = x^2 + y + y^3,  B = 1 + x + y^2
Cover: G = Z6 x Z6  (free Z2 double cover doubling x: Z6->Z3 mod 3),  same A,B.

Uses bb_lab's trusted primitives for construction + SAT exact distance, and
builds the cover/projection(p)/diagonal(tau)/deck(sigma) maps here, verifying
each is a genuine chain map before using the induced maps on H_1.
"""
from __future__ import annotations
import numpy as np

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, assert_css_commutation, circulant
from bb_lab.codeparams import code_params
from bb_lab.linalg import rref_f2, rank_f2, nullspace_f2, quotient_complement_basis
from bb_lab.sat_distance import x_distance, find_logical_z, _solve_at_weight

OK = "PASS"; BAD = "FAIL"
results = []
def check(name, cond, detail=""):
    tag = OK if cond else BAD
    results.append((tag, name, detail))
    print(f"  [{tag}] {name}" + (f"  -- {detail}" if detail else ""))
    return cond

def rowspace_basis(M):
    R, piv = rref_f2(M)
    return R[:len(piv)].copy()  # nonzero RREF rows = rowspace basis

def in_rowspace(M, x):
    """Is vector x in the F2 rowspace of M?"""
    r0 = rank_f2(M)
    r1 = rank_f2(np.vstack([M, x[None, :] & 1]))
    return r1 == r0

def classes_rank_mod(boundaries, images):
    """dim of span(images) modulo rowspace(boundaries)."""
    r_b = rank_f2(boundaries)
    r_all = rank_f2(np.vstack([boundaries, images]))
    return r_all - r_b

# ---------------------------------------------------------------- groups/polys
Gb = AbelianGroup((3, 6))      # base: x order 3, y order 6
Gc = AbelianGroup((6, 6))      # cover: x order 6, y order 6
Ab = Poly.from_string("x^2 + y + y^3", Gb); Bb = Poly.from_string("1 + x + y^2", Gb)
Ac = Poly.from_string("x^2 + y + y^3", Gc); Bc = Poly.from_string("1 + x + y^2", Gc)
print(f"base A={Ab.canonical_string()}  B={Bb.canonical_string()}  |Gb|={Gb.cardinality}")
print(f"cover A={Ac.canonical_string()}  B={Bc.canonical_string()}  |Gc|={Gc.cardinality}")

chb = bb_check_matrices(Ab, Bb); assert_css_commutation(chb)
chc = bb_check_matrices(Ac, Bc); assert_css_commutation(chc)
HXb, HZb = chb.H_X.astype(np.uint8), chb.H_Z.astype(np.uint8)
HXc, HZc = chc.H_X.astype(np.uint8), chc.H_Z.astype(np.uint8)

print("\n=== (n,k) and dim H_1 ===")
pb = code_params(chb); pc = code_params(chc)
check("base (n,k) = (36,4)", (pb.n, pb.k) == (36, 4), f"got ({pb.n},{pb.k})")
check("cover (n,k) = (72,4)", (pc.n, pc.k) == (72, 4), f"got ({pc.n},{pc.k})")
check("base dim H_1 = 4 (=k)", pb.k == 4)
check("cover dim H_1 = 4 (=k)", pc.k == 4)

print("\n=== exact distances (SAT) ===")
db = x_distance(chb, verbose=True, code_id="base"); print(f"  base  d = {db.distance}")
dc = x_distance(chc, verbose=True, code_id="cover"); print(f"  cover d = {dc.distance}")
check("base d = 4", db.distance == 4, f"got {db.distance}")
check("cover d = 8", dc.distance == 8, f"got {dc.distance}")
check("cover distance doubles base (8 = 2*4)", dc.distance == 2 * db.distance)

# ------------------------------------------------- cover maps p, tau, sigma
# pi: Gc=(x,y) -> Gb=(x mod 3, y). p = sum over fiber (pushforward), |Gb|x|Gc|.
nb, nc = Gb.cardinality, Gc.cardinality      # 18, 36
p_blk = np.zeros((nb, nc), dtype=np.uint8)
for h in Gc:
    p_blk[Gb.index((h[0] % 3, h[1])), Gc.index(h)] = 1
tau_blk = p_blk.T.copy()                      # diagonal lift = pullback = transpose
# sigma = deck = multiply by x^3 = translation by (3,0) on Gc
sig_blk = np.zeros((nc, nc), dtype=np.uint8)
for h in Gc:
    sig_blk[Gc.index(((h[0] + 3) % 6, h[1])), Gc.index(h)] = 1

def blkdiag(M):
    z = np.zeros_like(M)
    return np.block([[M, z], [z, M]])

P  = blkdiag(p_blk)     # C1^cov(72) -> C1^base(36)
T  = blkdiag(tau_blk)   # C1^base(36) -> C1^cov(72)
S  = blkdiag(sig_blk)   # C1^cov -> C1^cov

print("\n=== chain-map identities (validate the map construction) ===")
# p chain map:  d1: p_C0 @ HXc == HXb @ P  ;  d2: P @ HZc^T == HZb^T @ p_C0
check("p is a chain map for d1", np.array_equal((p_blk @ HXc) % 2, (HXb @ P) % 2))
check("p is a chain map for d2", np.array_equal((P @ HZc.T) % 2, (HZb.T @ p_blk) % 2))
# tau chain map: d1: HXc @ T == tau_C0 @ HXb ; d2: T @ HZb^T == HZc^T @ tau_C0
check("tau is a chain map for d1", np.array_equal((HXc @ T) % 2, (tau_blk @ HXb) % 2))
check("tau is a chain map for d2", np.array_equal((T @ HZb.T) % 2, (HZc.T @ tau_blk) % 2))
# sigma commutes with the boundary (deck is a chain automorphism)
check("sigma commutes with d1 (HXc@S == sig_C0@HXc)",
      np.array_equal((HXc @ S) % 2, (sig_blk @ HXc) % 2))
# p o tau = 0 (chain level) ; tau o p = 1 + sigma (chain level)
check("p o tau = 0 at chain level", np.array_equal((P @ T) % 2, np.zeros((36, 36), np.uint8)))
check("tau o p = 1 + sigma at chain level",
      np.array_equal((T @ P) % 2, (np.eye(72, dtype=np.uint8) ^ S) % 2))

# ------------------------------------------------- induced maps on H_1
LZb = find_logical_z(chb)   # base Z-logical reps (4 x 36), in ker HXb \ rowspan HZb
LZc = find_logical_z(chc)   # cover Z-logical reps (4 x 72)
check("base has 4 indep Z-logicals", LZb.shape[0] == 4)
check("cover has 4 indep Z-logicals", LZc.shape[0] == 4)

# p_* : H1(cover) -> H1(base).  rank = dim span{[p(rep_i)]} mod base boundaries
p_imgs = np.array([(P @ LZc[i]) % 2 for i in range(LZc.shape[0])], dtype=np.uint8)
# every image must be a base cycle (in ker HXb):
check("p sends cover cycles to base cycles",
      all(not ((HXb @ p_imgs[i]) % 2).any() for i in range(p_imgs.shape[0])))
rank_p = classes_rank_mod(HZb, p_imgs)
check("rank p_* = 2 (=> dangerous sector dim 2)", rank_p == 2, f"rank p_* = {rank_p}")

# tau_* : H1(base) -> H1(cover)
t_imgs = np.array([(T @ LZb[i]) % 2 for i in range(LZb.shape[0])], dtype=np.uint8)
check("tau sends base cycles to cover cycles",
      all(not ((HXc @ t_imgs[i]) % 2).any() for i in range(t_imgs.shape[0])))
rank_tau = classes_rank_mod(HZc, t_imgs)
check("rank tau_* = 2 (=> dim ker tau_* = 2 = dim im Delta)", rank_tau == 2, f"rank tau_* = {rank_tau}")

# homotopy theorem (R): sigma_* = id on H1(cover)  <=> sigma(rep)+rep is a boundary
R_ok = all(in_rowspace(HZc, (S @ LZc[i]) % 2 ^ LZc[i]) for i in range(LZc.shape[0]))
check("homotopy R: sigma_* = id on H_1(cover)", R_ok)

# linchpin: im p_* subset ker tau_*  <=>  tau_*(p_*(rep)) = 0 for every cover rep
linch = all(in_rowspace(HZc, (T @ ((P @ LZc[i]) % 2)) % 2) for i in range(LZc.shape[0]))
check("linchpin: im p_* ⊆ ker tau_* (= im Delta)", linch)

print("\n=== safe floor: classes reachable by p_* are HEAVY in the base ===")
# im p_* is a dim-2 subspace of H1(base); pick 2 independent reps mod base boundaries
Sb = rowspace_basis(HZb)                       # base Z-stabilizer basis
reps = []
for i in range(p_imgs.shape[0]):
    cand = p_imgs[i]
    test = np.vstack([HZb] + ([np.array(reps)] if reps else []) + [cand[None, :]])
    if rank_f2(test) > rank_f2(np.vstack([HZb] + ([np.array(reps)] if reps else []))):
        reps.append(cand)
check("im p_* has dimension 2", len(reps) == 2, f"got {len(reps)}")
r1, r2 = reps[0], reps[1]
class_reps = {"r1": r1, "r2": r2, "r1+r2": (r1 ^ r2)}

def coset_min_weight(rep, basis):
    d = basis.shape[0]
    coeffs = ((np.arange(1 << d)[:, None] >> np.arange(d)) & 1).astype(np.uint8)
    coset = (coeffs @ basis) % 2          # 2^d x n
    coset ^= rep[None, :]
    return int(coset.sum(axis=1).min())

print(f"  (base distance is {db.distance}; reachable classes should still be >= 8)")
all_heavy = True
for name, rep in class_reps.items():
    w = coset_min_weight(rep, Sb)
    print(f"    class {name:6s}: base coset-min weight = {w}")
    all_heavy &= (w >= 8)
check("all 3 reachable (safe) classes have base min weight >= 8", all_heavy)

print("\n=== upper bound: diagonal lift of the cheap base logical ===")
# get a weight-4 base Z-logical u* directly (Z-side SAT): v in ker HXb anticommuting an X-logical
LXb = quotient_complement_basis(HXb, nullspace_f2(HZb))   # base X-logical reps
ustar = None
for w in range(1, 8):
    wit, _ = _solve_at_weight(HXb, LXb, w)
    if wit is not None:
        ustar = (wit & 1).astype(np.uint8); break
check("found base Z-logical u*", ustar is not None)
check("u* has weight 4", int(ustar.sum()) == 4, f"weight {int(ustar.sum())}")
check("u* is a base cycle (HXb u* = 0)", not ((HXb @ ustar) % 2).any())
check("u* is nontrivial (not a base Z-stabilizer)", not in_rowspace(HZb, ustar))
tau_u = (T @ ustar) % 2
check("[u*] ∉ ker tau_* : tau(u*) is a NONtrivial cover logical",
      not in_rowspace(HZc, tau_u))
check("tau(u*) is a cover cycle (HXc = 0)", not ((HXc @ tau_u) % 2).any())
check("tau(u*) has weight 8 = 2*4", int(tau_u.sum()) == 8, f"weight {int(tau_u.sum())}")
check("tau(u*) is DANGEROUS (p(tau(u*)) = 0)", not ((P @ tau_u) % 2).any())

# ------------------------------------------------------------------- summary
print("\n" + "=" * 64)
n_fail = sum(1 for t, _, _ in results if t == BAD)
print(f"SUMMARY: {len(results)-n_fail}/{len(results)} checks PASS, {n_fail} FAIL")
if n_fail:
    for t, name, d in results:
        if t == BAD:
            print(f"   FAIL: {name}  {d}")

"""S3.0 data generator for the Stage-3 doubling instance (doc-verified pair).

Pair: base [[36,4,4]] on Z3 x Z6, A = x^2 + y + y^3, B = 1 + x + y^2;
x-cover [[72,4,8]] on Z6 x Z6 (deck (3,0)), same polynomials.
(The extensibility-doc §5 pair; chosen over the A9 q1=0 candidates after
the seam gate: every Z3xZ6 y-cover q1=0 candidate has 6-18 seam-hostile
light classes under the identity section, while this pair has ZERO — see
notes/A9_lean_target_screen.md, stage-3 gating addendum.)

All computations in the REPO convention (BBChainComplex.lean):
    d2 f = (A*f | B*f), d1 (cL,cR) = B*cL + A*cR,
    dualBoundary (wL,wR) = MA^T wL + MB^T wR.

Emits (hard asserts; nonzero exit on failure):
  1. parameters + SAT distances (base d=4, cover d=8);
  2. dim-2 systematic ker d2 basis + free cells + C-certificate pairs;
  3. the homotopy polynomial p with p * Bc = 1 + x^3 over F2[Z6xZ6]
     (whence the homotopy chain z = p * v_R: gross-shaped, one identity);
  4. weight-4 u* with tau(u*) a nontrivial cover logical + dual flux
     witness w (dual cycle, odd pairing with tau(u*));
  5. light-boundary census at weight <= 7 (exactly 24 weight-6
     boundaries; mu_Z = 6) and a seam-good preimage f0 for EVERY light
     boundary (expected to pass — the reason this pair was chosen);
  6. JSON (data/a9/pair72_z6z6_data.json) + Lean-ready supports.

Usage:  uv run python scripts/gen_pair72_z6z6_data.py
"""

from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.linalg import rank_f2, rref_f2, nullspace_f2
from bb_lab.sat_distance import x_distance

A_STR, B_STR = "x^2 + y + y^3", "1 + x + y^2"
ELL, M = 3, 6            # base Z3 x Z6
DECK = (3, 0)            # deck on the cover Z6 x Z6 (x-doubling)

fails: list[str] = []


def check(name: str, cond: bool, detail: str = "") -> bool:
    tag = "PASS" if cond else "FAIL"
    print(f"  [{tag}] {name}" + (f"  -- {detail}" if detail else ""))
    if not cond:
        fails.append(name)
    return cond


def solve_f2(Amat: np.ndarray, b: np.ndarray) -> np.ndarray | None:
    Amat = Amat.astype(np.uint8) % 2
    b = b.astype(np.uint8) % 2
    aug = np.hstack([Amat, b[:, None]])
    R, piv = rref_f2(aug)
    ncols = Amat.shape[1]
    if ncols in piv:
        return None
    x = np.zeros(ncols, dtype=np.uint8)
    for r, c in enumerate(piv):
        x[c] = R[r, ncols]
    return x


# ---------------------------------------------------------------- setup
Gb = AbelianGroup((ELL, M))
Gc = AbelianGroup((2 * ELL, M))
nb, nc = Gb.cardinality, Gc.cardinality  # 18, 36
Ab = Poly.from_string(A_STR, Gb)
Bb = Poly.from_string(B_STR, Gb)
Ac = Poly(support=frozenset(Ab.support), group=Gc)
Bc = Poly(support=frozenset(Bb.support), group=Gc)
base_idx = {g: i for i, g in enumerate(Gb)}
cover_idx = {g: i for i, g in enumerate(Gc)}
MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
MAc, MBc = circulant(Ac).astype(np.uint8), circulant(Bc).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2
D1b = np.hstack([MBb, MAb]) % 2
D2c = np.vstack([MAc, MBc]) % 2
D1c = np.hstack([MBc, MAc]) % 2
DUALc = np.hstack([MAc.T, MBc.T]) % 2

print("== 1. parameters and distances ==")
chb, chc = bb_check_matrices(Ab, Bb), bb_check_matrices(Ac, Bc)
pb, pc = code_params(chb), code_params(chc)
check("base (n,k) = (36,4)", (pb.n, pb.k) == (36, 4), f"got {(pb.n, pb.k)}")
check("cover (n,k) = (72,4)", (pc.n, pc.k) == (72, 4), f"got {(pc.n, pc.k)}")
db = x_distance(chb, code_id="base36").distance
dc = x_distance(chc, weight_upper_bound=8, code_id="cover72").distance
check("base d = 4", db == 4, f"got {db}")
check("cover d = 8 (UNSAT through 7)", dc == 8, f"got {dc}")
check("repo d1 o d2 = 0 (base)", not ((D1b @ D2b) % 2).any())
check("repo d1 o d2 = 0 (cover)", not ((D1c @ D2c) % 2).any())

# ------------------------------------------------- 2. ker d2 + certificate
print("== 2. systematic ker d2 basis + C certificate ==")
ker = nullspace_f2(D2b)
check("dim ker d2 = 2", ker.shape[0] == 2, f"got {ker.shape[0]}")
free_cells = None
kb = None
for i, j in itertools.combinations(range(nb), 2):
    sub = ker[:, [i, j]] % 2
    det = (sub[0, 0] & sub[1, 1]) ^ (sub[0, 1] & sub[1, 0])
    if det == 1:
        inv = np.array([[sub[1, 1], sub[0, 1]], [sub[1, 0], sub[0, 0]]], dtype=np.uint8)
        kb = (inv @ ker) % 2
        free_cells = (i, j)
        break
assert free_cells is not None and kb is not None
check("systematic basis at free cells", kb[0, free_cells[0]] == 1
      and kb[0, free_cells[1]] == 0 and kb[1, free_cells[0]] == 0
      and kb[1, free_cells[1]] == 1)
check("kb in ker d2", not ((D2b @ kb.T) % 2).any())

recon_targets = np.zeros((nb, nb), dtype=np.uint8)
for g in range(nb):
    r = (kb[0] * (1 if free_cells[0] == g else 0)) ^ (kb[1] * (1 if free_cells[1] == g else 0))
    r = r.copy()
    r[g] ^= 1
    recon_targets[:, g] = r
C_mat = np.zeros((nb, 2 * nb), dtype=np.uint8)
ok = True
for h in range(nb):
    x = solve_f2(D2b.T, recon_targets[h, :])
    if x is None:
        ok = False
        break
    C_mat[h] = x
check("C certificate solvable", ok)
if ok:
    check("C certificate verifies", np.array_equal((C_mat @ D2b) % 2, recon_targets))
c_pairs = [(h, p) for h in range(nb) for p in range(2 * nb) if C_mat[h, p]]
print(f"  |cPairs| = {len(c_pairs)}")

# ------------------------------------------------- 3. homotopy polynomial p
print("== 3. homotopy polynomial p (p * Bc = 1 + x^3) ==")
target = np.zeros(nc, dtype=np.uint8)
target[cover_idx[(0, 0)]] ^= 1
target[cover_idx[DECK]] ^= 1
p_poly = solve_f2(MBc, target)
check("p * Bc = 1 + x^3 solvable", p_poly is not None)
if p_poly is not None:
    check("p verifies", np.array_equal((MBc @ p_poly) % 2, target))
    p_supp = sorted(g for g in Gc if p_poly[cover_idx[g]])
    print(f"  p support ({int(p_poly.sum())} cells): {p_supp}")

# ------------------------------------------------- 4. u* + dual flux witness
print("== 4. tight witness u* + cover dual flux witness ==")
in_rowspace = lambda Mrows, x: rank_f2(np.vstack([Mrows, x[None, :] & 1])) == rank_f2(Mrows)
Sb_rows = D2b.T
Sc_rows = D2c.T
tau_mat = np.zeros((2 * nc, 2 * nb), dtype=np.uint8)
for g in Gc:
    pg = (g[0] % ELL, g[1])
    for blk in range(2):
        tau_mat[blk * nc + cover_idx[g], blk * nb + base_idx[pg]] = 1

ustar = None
for supp in itertools.combinations(range(2 * nb), 4):
    v = np.zeros(2 * nb, dtype=np.uint8)
    v[list(supp)] = 1
    if ((D1b @ v) % 2).any():
        continue
    if in_rowspace(Sb_rows, v):
        continue
    tv = (tau_mat @ v) % 2
    if in_rowspace(Sc_rows, tv):
        continue
    ustar = v
    break
check("weight-4 u* with tau(u*) nontrivial found", ustar is not None)
uL = uR = wL = wR = None
if ustar is not None:
    uL = sorted(g for g in Gb if ustar[base_idx[g]])
    uR = sorted(g for g in Gb if ustar[nb + base_idx[g]])
    print(f"  u* left block: {uL}   right block: {uR}")
    tau_u = (tau_mat @ ustar) % 2
    kerD = nullspace_f2(DUALc)
    pair = (kerD @ tau_u) % 2
    idx = np.nonzero(pair)[0]
    check("dual cycle with odd pairing exists", idx.size > 0)
    w = kerD[idx[0]].astype(np.uint8)
    # greedy sparsification over the even-pairing kernel vectors
    others = [kerD[i] for i in range(kerD.shape[0]) if i != idx[0]]
    improved = True
    while improved:
        improved = False
        for o in others:
            if int((o @ tau_u) % 2) == 0:
                cand = (w ^ o) % 2
                if cand.sum() < w.sum():
                    w = cand
                    improved = True
    check("w is a dual cycle", not ((DUALc @ w) % 2).any())
    check("<w, tau(u*)> = 1", int((w @ tau_u) % 2) == 1)
    wL = sorted(g for g in Gc if w[cover_idx[g]])
    wR = sorted(g for g in Gc if w[nc + cover_idx[g]])
    print(f"  flux witness weight {int(w.sum())}; left: {wL}")
    print(f"    right: {wR}")

# ------------------------------------------------- 5. census + seam reps
print("== 5. light-boundary census (weight <= 7) + seam-good reps ==")
L2 = np.zeros((nc, nb), dtype=np.uint8)
for h in Gb:
    L2[cover_idx[h], base_idx[h]] = 1  # identity section (x in {0..2})
LS = (D2c @ L2) % 2
sheet0_rows = np.zeros((2 * nb, 2 * nc), dtype=np.uint8)
for h in Gb:
    for blk in range(2):
        sheet0_rows[blk * nb + base_idx[h], blk * nc + cover_idx[h]] = 1
SEAM0 = (sheet0_rows @ LS) % 2
kercombos = [np.zeros(nb, dtype=np.uint8), kb[0] % 2, kb[1] % 2, (kb[0] ^ kb[1]) % 2]

img_basis = rref_f2(D2b.T)[0][: rank_f2(D2b.T)]
dim_img = img_basis.shape[0]
check("dim im d2 = 16", dim_img == 16, f"got {dim_img}")
census: dict[int, int] = {}
mu_z = None
light: list[np.ndarray] = []
exps = np.arange(dim_img, dtype=np.uint64)
for start in range(0, 1 << dim_img, 1 << 14):
    idxs = np.arange(start, min(start + (1 << 14), 1 << dim_img), dtype=np.uint64)
    coeffs = ((idxs[:, None] >> exps[None, :]) & 1).astype(np.uint8)
    block = (coeffs @ img_basis) % 2
    wts = block.sum(axis=1)
    nz = wts[wts > 0]
    if nz.size:
        m0 = int(nz.min())
        mu_z = m0 if mu_z is None or m0 < mu_z else mu_z
    for wt in range(2, 8):
        cnt = int((wts == wt).sum())
        if cnt:
            census[wt] = census.get(wt, 0) + cnt
            for row in block[wts == wt]:
                light.append(row.copy())
print(f"  census (weights <= 7): {census}, mu_Z = {mu_z}")
check("census = 24 weight-6 boundaries only", census == {6: 24})
check("mu_Z = 6", mu_z == 6)

seam_good_all = True
f0_data = []
for b in light:
    f = solve_f2(D2b, b)
    assert f is not None
    good = None
    for zi, zeta in enumerate(kercombos):
        f0 = (f ^ zeta) % 2
        seam = (SEAM0 @ f0) % 2
        if np.all((seam & (1 - b)) == 0):
            good = (f0, zi)
            break
    if good is None:
        seam_good_all = False
    else:
        f0_data.append({
            "b_support": [[int(pq // nb), list(list(Gb)[pq % nb])] for pq in np.nonzero(b)[0]],
            "f0_support": [list(list(Gb)[h]) for h in np.nonzero(good[0])[0]],
        })
check("EVERY weight-6 boundary has a seam-good f0 in its ker-coset", seam_good_all)

# also: the Lean classification statement's per-f existential is over the
# 4-element ker-coset of f itself; confirm the equivalent sweep form:
#   forall f, d2 f != 0 and wt(d2 f) <= 7  ->  wt(d2 f) = 6 and
#     exists zeta in kercombos, seamOK(f + zeta)
# (this is what the census + scan above verified, boundary-by-boundary).

out = {
    "instance_id": "doc_pair_ext5",
    "A": A_STR, "B": B_STR,
    "base_group": [ELL, M], "cover_group": [2 * ELL, M], "deck": list(DECK),
    "d_base": int(db), "d_cover": int(dc),
    "free_cells": [list(list(Gb)[free_cells[0]]), list(list(Gb)[free_cells[1]])],
    "kb0_support": [list(g) for g in Gb if kb[0][base_idx[g]]],
    "kb1_support": [list(g) for g in Gb if kb[1][base_idx[g]]],
    "c_pairs": [[h, p] for h, p in c_pairs],
    "p_support": [list(g) for g in p_supp] if p_poly is not None else None,
    "ustar_left": [list(g) for g in uL] if uL is not None else None,
    "ustar_right": [list(g) for g in uR] if uR is not None else None,
    "flux_left": [list(g) for g in wL] if wL is not None else None,
    "flux_right": [list(g) for g in wR] if wR is not None else None,
    "census": census, "mu_Z": mu_z,
    "f0_reps": f0_data,
}
outp = LAB_ROOT / "data" / "a9" / "pair72_z6z6_data.json"
outp.parent.mkdir(parents=True, exist_ok=True)
outp.write_text(json.dumps(out, indent=1))
print(f"\nwrote {outp}")

print("\n" + "=" * 60)
if fails:
    print(f"RESULT: {len(fails)} FAILURES: {fails}")
    sys.exit(1)
print("RESULT: ALL CHECKS PASS")

# ------------------------------------------------- 5b. seam tables (Lean literals)
# The three class seams seamC (kcombo c0 c1) as literal supports, consumed by
# QEC/.../Z3Z6/SeamTables.lean (tabulated so the SweepSafe* leaves do not
# re-derive a 72-entry constant 2^18 times).
print("== 5b. tabulated class seams ==")
S1 = np.zeros((2 * nb, 2 * nc), dtype=np.uint8)
for h in Gb:
    hp = ((h[0] + 3) % (2 * ELL), h[1])
    for blk in range(2):
        S1[blk * nb + base_idx[h], blk * nc + cover_idx[hp]] = 1
SEAM1 = (S1 @ LS) % 2
for (c0, c1), name in [((1, 0), "seam10"), ((0, 1), "seam01"), ((1, 1), "seam11")]:
    z = (c0 * kb[0] ^ c1 * kb[1]) % 2
    s = (SEAM1 @ z) % 2
    L = sorted(g for g in Gb if s[base_idx[g]])
    R = sorted(g for g in Gb if s[nb + base_idx[g]])
    print(f"  {name}: wt={int(s.sum())}  L={L}  R={R}")
    out[name] = {"L": [list(g) for g in L], "R": [list(g) for g in R]}
outp.write_text(json.dumps(out, indent=1))

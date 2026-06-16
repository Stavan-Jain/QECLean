"""A3 / Track 1.1 Entry 10 — rigidity engine: per-block shape analysis.

Hand-proof architecture for the 28 profile families (Entry 9): pivot on ONE
block. For a light b = (Bz, Az):

  (1) ENGINE. For an A-radical component j (j in {1,3,4}), V_j^A = A_j z_j
      lies in the 2-dim ideal (A_j) = {a A_j + c uv}; since the three nonzero
      values of A_j are pairwise distinct and nonzero, every nonzero ideal
      element has support = a co-point or all of Z2^2, and the value vector
      on its support is a FIXED vector C_j(s4) up to one scalar. Hence the
      ratios V_j^A[s]/V_j^A[s'] are explicit constants, and delta-point
      layers (whose component values are character evaluations psi_j(t))
      yield equations psi_j(t_i - t_k) = C_j ratios that pin cell
      differences (psi_3, psi_4 separate Z3^2).

  (2) ENDGAME. If the A-block is pinned to A.(delta_g) (or A.(D-pair)),
      subtract: z = g + z' with z' in Ann(A); then b - hexagon = (B z', 0)
      is a ONE-BLOCK codeword, and the one-block lemma (|B z'| = 0 or >= a
      floor > 10) forces z' in ker d2, i.e. b IS the hexagon (D-pair).

This script machine-verifies each ingredient:
  G1  the C-catalog: for both blocks' radical components, ideal supports
      are co-point-or-full and value vectors are rigid up to scalar;
  G2  one-block lemmas: exact min weight of (B z', 0), z' in Ann(A)\ker
      (4096-element enumeration; expect >= 12), and symmetrically (0, A z');
  G3  R1 shape classification: the weight-3 elements of im(A.) with three
      1-point layers are EXACTLY the 36 hexagon A-blocks A.delta_g;
  G4  the master per-shape table: for every A-side layer profile S occurring
      in the Entry-9 families, classify {f in im(A.) : shape S} up to
      translation and compute mu_B(f) = min |B(z0 + z')| over the Ann(A)
      coset; report min |f| + mu_B per shape (expect 6 for {1,1,1}, 10 for
      {2,1,1}, > 10 or empty for all other shapes). By the x<->y swap
      symmetry (A(x,y) = B(y,x)) the B-side tables are mirror images.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import combinations, product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, rank_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm = bb_check_matrices(Ab, Bb)
HZb = cm.H_Z & 1
d2b = HZb.T
nb = 36
B_map, A_map = d2b[:nb, :], d2b[nb:, :]          # b = (B z | A z)

# ---------------------------------------------------------- F4 + transforms
F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        c0 = (a0 & b0) ^ (a1 & b1)
        c1 = (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)
        F4_MUL[a, b_] = c0 | (c1 << 1)
def f4mul(a, b): return int(F4_MUL[a, b])
def f4inv(a): return {1: 1, 2: 3, 3: 2}[a]
W4 = [1, 2, 3]                                    # 1, w, w^2 as powers of w

ORBITS = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, 2, 3]

def s_of(a, b): return (a % 2) | ((b % 2) << 1)

def field_hat(fvec):
    out = {}
    for j, (c, d) in ORBITS.items():
        e = [0, 0, 0, 0]
        for g in Gb:
            if fvec[Gb.index(g)]:
                a, b = g
                e[s_of(a, b)] ^= WPOW[(c * (a % 3) + d * (b % 3)) % 3]
        out[j] = tuple(e)
    return out

AH = field_hat((A_map @ np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]) % 2)
BH = field_hat((B_map @ np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]) % 2)

# ------------------------------------------------------------ G1: C-catalog
print("=== G1: ideal rigidity catalog (radical components, both blocks) ===")
def ideal_elements(gen):
    uv = (1, 1, 1, 1)
    out = set()
    for a in range(4):
        for c in range(4):
            e = tuple(f4mul(a, gen[s]) ^ f4mul(c, uv[s]) for s in range(4))
            out.add(e)
    return out

ok_g1 = True
for name, gen, rad in (("A1", AH[1], True), ("A3", AH[3], True), ("A4", AH[4], True),
                       ("B2", BH[2], True), ("B3", BH[3], True), ("B4", BH[4], True)):
    elems = ideal_elements(gen)
    sup_sizes = sorted({sum(1 for v in e if v) for e in elems})
    ok_g1 &= (sup_sizes == [0, 3, 4])
    # rigidity: for each co-point, the elements vanishing there form one
    # F4-line (value vector unique up to scalar)
    for s4 in range(4):
        line = [e for e in elems if e[s4] == 0 and any(e)]
        reps = {tuple(f4mul(f4inv(next(v for v in e if v)), x) for x in e) for e in line}
        ok_g1 &= (len(reps) == 1)
    vals = [v for v in gen if v]
    ok_g1 &= (len(set(vals)) == 3)
print(f"  supports are co-point-or-full and values rigid up to scalar: {ok_g1}")

# -------------------------------------------------------- G2: one-block min
print("\n=== G2: one-block lemmas (exact, full enumeration of Ann) ===")
AnnA = nullspace_f2(A_map)                        # dim 12
AnnB = nullspace_f2(B_map)
ker = nullspace_f2(d2b)                           # dim 6
def span_set(rows):
    out = set()
    for mask in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (mask >> i) & 1:
                v ^= rows[i]
        out.add(v.tobytes())
    return out
ker_set = span_set(ker)
def one_block_min(Ann, other_map):
    best = None
    for mask in range(1 << Ann.shape[0]):
        z = np.zeros(nb, np.uint8)
        for i in range(Ann.shape[0]):
            if (mask >> i) & 1:
                z ^= Ann[i]
        if z.tobytes() in ker_set:
            continue
        w = int(((other_map @ z) % 2).sum())
        if best is None or w < best:
            best = w
    return best
mB = one_block_min(AnnA, B_map)
mA = one_block_min(AnnB, A_map)
print(f"  min |B z'| over Ann(A) \\ ker: {mB}  (claim: >= 12)")
print(f"  min |A z'| over Ann(B) \\ ker: {mA}  (claim: >= 12)")

# --------------------------------------------------- G3: R1 classification
print("\n=== G3: weight-3 three-delta-layer elements of im(A.) ===")
KA_dual = nullspace_f2(A_map.T)                   # f in im(A.) iff KA_dual f = 0
def crt_idx(s, t):
    sx, sy = s & 1, (s >> 1) & 1
    tx, ty = t // 3, t % 3
    return Gb.index(((3 * sx + 4 * tx) % 6, (3 * sy + 4 * ty) % 6))
LAYER_CELLS = [[crt_idx(s, t) for t in range(9)] for s in range(4)]

hex_blocks = set()
for g in Gb:
    f = (A_map @ np.eye(nb, dtype=np.uint8)[Gb.index(g)]) % 2
    hex_blocks.add(f.tobytes())
found = set()
for L in combinations(range(4), 3):
    for ts in product(range(9), repeat=3):
        f = np.zeros(nb, np.uint8)
        for s, t in zip(L, ts):
            f[LAYER_CELLS[s][t]] = 1
        if not ((KA_dual @ f) % 2).any():
            found.add(f.tobytes())
print(f"  shape-(1,1,1) elements of im(A.): {len(found)}; "
      f"hexagon A-blocks: {len(hex_blocks)}; equal: {found == hex_blocks}")

# --------------------------------------------------- G4: master shape table
print("\n=== G4: per-shape im(A.) classification + mu_B completion costs ===")
def f2_solve(A, rhs):
    A = (A & 1).astype(np.uint8); rhs = (rhs & 1).astype(np.uint8)
    m, k = A.shape
    Aug = np.concatenate([A, rhs.reshape(-1, 1)], axis=1)
    piv_row = 0; piv_cols = []
    for col in range(k):
        nz = np.flatnonzero(Aug[piv_row:, col])
        if nz.size == 0:
            continue
        r = piv_row + int(nz[0])
        if r != piv_row:
            Aug[[piv_row, r]] = Aug[[r, piv_row]]
        msk = Aug[:, col] == 1; msk[piv_row] = False
        if msk.any():
            Aug[msk] ^= Aug[piv_row]
        piv_cols.append(col); piv_row += 1
        if piv_row == m:
            break
    x = np.zeros(k, np.uint8)
    for i, col in enumerate(piv_cols):
        x[col] = Aug[i, k]
    return x

AnnA_all = []                                     # all 4096 annihilator elements
for mask in range(1 << AnnA.shape[0]):
    z = np.zeros(nb, np.uint8)
    for i in range(AnnA.shape[0]):
        if (mask >> i) & 1:
            z ^= AnnA[i]
    AnnA_all.append(z)
AnnA_mat = np.array(AnnA_all, dtype=np.uint8)
B_of_Ann = (AnnA_mat @ B_map.T) % 2               # 4096 x 36

def mu_B(f):
    z0 = f2_solve(A_map, f)
    base = (B_map @ z0) % 2
    return int(((B_of_Ann ^ base).sum(axis=1)).min())

def translate(f, dx, dy):
    out = np.zeros_like(f)
    for g in Gb:
        out[Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = f[Gb.index(g)]
    return out

SHAPES = [(1, 1, 1), (1, 1, 1, 1), (2, 1, 1), (2, 1, 1, 1), (2, 2, 1),
          (2, 2, 1, 1), (3, 1, 1), (3, 1, 1, 1), (3, 2, 1), (3, 2, 1, 1),
          (3, 3, 1), (4, 1, 1), (4, 1, 1, 1), (5, 1, 1)]
for shape in SHAPES:
    n_lay = len(shape)
    reps = {}                                     # canonical -> (|f|, mu_B)
    for L in combinations(range(4), n_lay):
        for ws in set(__import__("itertools").permutations(shape)):
            pools = [list(combinations(range(9), w)) for w in ws]
            for choice in product(*pools):
                f = np.zeros(nb, np.uint8)
                for s, T in zip(L, choice):
                    for t in T:
                        f[LAYER_CELLS[s][t]] = 1
                if ((KA_dual @ f) % 2).any():
                    continue
                canon = min(translate(f, dx, dy).tobytes()
                            for dx in range(6) for dy in range(6))
                if canon not in reps:
                    reps[canon] = (int(f.sum()), mu_B(f))
    if not reps:
        print(f"  shape {shape}: NO elements of im(A.)")
        continue
    vals = sorted(w + m for w, m in reps.values())
    n_light = sum(1 for w, m in reps.values() if w + m <= 10)
    print(f"  shape {shape}: {len(reps)} translation classes; "
          f"min |f|+mu_B = {vals[0]}; classes with |f|+mu_B <= 10: {n_light}")

print("\nDone.")

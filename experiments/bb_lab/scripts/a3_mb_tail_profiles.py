"""A3 / Track 1.1 Entry 9 — tail attack II: layer-profile completeness + family checks.

Reduction of the (T-tail) equality analysis to an explicit finite case list.
Write any b = (Bz, Az) in s-layers over the CRT splitting Z6^2 = Z2^2 x Z3^2
(layer s in Z2^2 carries a function on Z3^2, weights w_s^B, w_s^A in [0,9]).

Three completeness lemmas (P1 verifies; (i),(iii) are hand-proven, (ii) is the
Entry-8 component-support lemma, machine-verified):
  (i)   PARITY: the two blocks have identical layer parities. Proof: the
        layer parity vector of a block is its component-0 transform, and
        A and B have the same s-parts {1, s_x, s_y}, so A_0 = B_0 = [1] +
        [s_x] + [s_y] and both blocks see w0 = A_0 z_0.
  (ii)  FLOOR: each block is supported on >= 3 layers (component 4 is alive
        for |b| <= 11 and its radical ideal has co-point-or-full supports).
  (iii) EVEN: |b| is even (|Az| = |Bz| = |z| mod 2).

Consequently, for |b| <= 10 the pair of layer-weight vectors (w^B, w^A) must
satisfy: parities equal layerwise, >= 3 nonzero layers each, total <= 10.
P2 enumerates ALL such weight-vector pairs (the profile families).

P3 then checks each family EXHAUSTIVELY: enumerate all layer contents
(subsets of Z3^2 of the prescribed sizes) for both blocks and keep exactly
the pairs forming a genuine stabilizer (b in colspan d2). Membership is a
42-bit syndrome hash-join: K = ker(d2^T), and b in colspan(d2) iff
K_B b_B = K_A b_A. Survivors are classified (hexagon / D-pair / OTHER).

Expected: {1,1,1}+{1,1,1} -> the 36 hexagons; {1,1,2}+{1,1,2,2} families ->
the 216 D-pairs; every other family EMPTY. That reduces (T-tail) to the
three lemmas + this finite case analysis.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import combinations, product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm = bb_check_matrices(Ab, Bb)
HZb = cm.H_Z & 1
d2b = HZb.T                                   # z (36) -> b = (Bz | Az) (72)
nb = 36

K = nullspace_f2(d2b.T)                       # 42 x 72; b in colspan(d2) iff K b = 0
KB, KA = K[:, :nb], K[:, nb:]

# CRT cell map: layer s = (sx, sy) in Z2^2, t = (tx, ty) in Z3^2
def crt_idx(s, t):
    sx, sy = s & 1, (s >> 1) & 1
    tx, ty = t // 3, t % 3
    a = (3 * sx + 4 * tx) % 6
    b = (3 * sy + 4 * ty) % 6
    return Gb.index((a, b))

LAYER_CELLS = [[crt_idx(s, t) for t in range(9)] for s in range(4)]

def block_layers(block_vec):
    return [int(sum(block_vec[LAYER_CELLS[s][t]] for t in range(9))) for s in range(4)]

# ------------------------------------------------------------- P1: lemmas
print("=== P1: completeness-lemma verification on random z ===")
rng = np.random.default_rng(20260612)
ok_par = ok_floor = True
for _ in range(300):
    z = rng.integers(0, 2, nb, dtype=np.uint8)
    b = (d2b @ z) % 2
    wB = block_layers(b[:nb]); wA = block_layers(b[nb:])
    ok_par &= all((wA[s] % 2) == (wB[s] % 2) for s in range(4))
    if 0 < int(b.sum()) <= 11:
        ok_floor &= (sum(1 for w in wA if w) >= 3 and sum(1 for w in wB if w) >= 3)
print(f"  identical layer parities across blocks: {ok_par}")
print(f"  (floor only spot-checked; light b rarely sampled randomly)")

# ----------------------------------------------- P2: profile-pair families
print("\n=== P2: all (w^A, w^B) layer-weight pairs for |b| <= 10 ===")
vecs = [v for v in product(range(10), repeat=4)
        if sum(1 for x in v if x) >= 3 and 0 < sum(v) <= 7]
pairs = []
for va in vecs:                               # va = A-block weights
    for vb in vecs:
        if sum(va) + sum(vb) > 10:
            continue
        if any((va[s] % 2) != (vb[s] % 2) for s in range(4)):
            continue
        pairs.append((va, vb))
fams = {}
for va, vb in pairs:
    keyf = (tuple(sorted((x for x in va if x), reverse=True)),
            tuple(sorted((x for x in vb if x), reverse=True)))
    fams.setdefault(keyf, []).append((va, vb))
print(f"  placements: {len(pairs)}, profile families: {len(fams)}")
for keyf in sorted(fams):
    print(f"    A {keyf[0]} + B {keyf[1]}: |b| = {sum(keyf[0]) + sum(keyf[1])}, "
          f"{len(fams[keyf])} placements")

# ------------------------------------------------- P3: exhaustive families
print("\n=== P3: exhaustive content check per family (syndrome hash-join) ===")

def pack_key(bits):
    return int.from_bytes(np.packbits(bits).tobytes(), "big")

# per (side, layer, weight): list of (content-tuple, key)
SUBKEYS = {}
def subkeys(side_mat, s, w):
    keyid = (id(side_mat), s, w)
    if keyid not in SUBKEYS:
        out = []
        for T in combinations(range(9), w):
            vec = np.zeros(nb, np.uint8)
            for t in T:
                vec[LAYER_CELLS[s][t]] = 1
            out.append((T, pack_key((side_mat @ vec) % 2)))
        SUBKEYS[keyid] = out
    return SUBKEYS[keyid]

def enumerate_side(side_mat, wvec):
    """yield (contents, key) for one block with exact layer weights wvec."""
    layers = [s for s in range(4) if wvec[s]]
    pools = [subkeys(side_mat, s, wvec[s]) for s in layers]
    def rec(i, acc_key, acc_cont):
        if i == len(layers):
            yield tuple(acc_cont), acc_key
            return
        for T, k in pools[i]:
            yield from rec(i + 1, acc_key ^ k, acc_cont + [(layers[i], T)])
    yield from rec(0, 0, [])

def vec_of(contents, offset):
    v = np.zeros(2 * nb, np.uint8)
    for s, T in contents:
        for t in T:
            v[offset + LAYER_CELLS[s][t]] = 1
    return v

ker_d2b = nullspace_f2(d2b)

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

def classify(bvec):
    z0 = f2_solve(d2b, bvec)
    if (((d2b @ z0) % 2) ^ bvec).any():
        return "NOT-A-STABILIZER?!"
    best = None
    for mask in range(1 << ker_d2b.shape[0]):
        z = z0.copy()
        for i in range(ker_d2b.shape[0]):
            if (mask >> i) & 1:
                z ^= ker_d2b[i]
        w = int(z.sum())
        if best is None or w < best[0]:
            best = (w, z.copy())
    k_min, z = best
    if k_min == 1:
        return "HEXAGON"
    if k_min == 2:
        return "D-PAIR"
    return f"OTHER(k_min={k_min})"

totals = {}
for keyf in sorted(fams):
    survivors = []
    for va, vb in fams[keyf]:
        a_index = {}
        for cont, key in enumerate_side(KA, va):
            a_index.setdefault(key, []).append(cont)
        for contB, keyB in enumerate_side(KB, vb):
            if keyB in a_index:
                for contA in a_index[keyB]:
                    b = vec_of(contA, nb) ^ vec_of(contB, 0)
                    survivors.append(b)
    kinds = {}
    for b in survivors:
        kinds[classify(b)] = kinds.get(classify(b), 0) + 1
    totals[keyf] = kinds
    tag = ", ".join(f"{k}: {v}" for k, v in sorted(kinds.items())) if kinds else "EMPTY"
    print(f"  A {keyf[0]} + B {keyf[1]} (|b| = {sum(keyf[0]) + sum(keyf[1])}): {tag}")

n_other = sum(v for kinds in totals.values() for k, v in kinds.items() if k.startswith("OTHER") or k.startswith("NOT"))
n_hex = sum(v for kinds in totals.values() for k, v in kinds.items() if k == "HEXAGON")
n_pair = sum(v for kinds in totals.values() for k, v in kinds.items() if k == "D-PAIR")
print(f"\n  TOTALS: hexagons {n_hex} (expect 36), D-pairs {n_pair} (expect 216), "
      f"others {n_other} (expect 0)")
print("  => if others = 0: every b with |b| <= 10 is a hexagon or a D-pair,")
print("     conditional on lemmas (i)-(iii); (T-tail) reduces to these finite checks.")
print("\nDone.")

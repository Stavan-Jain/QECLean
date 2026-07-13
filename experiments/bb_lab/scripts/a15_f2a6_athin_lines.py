"""A15 near-kernel classification, step 5: the A-thin layer.

By the sigma-reduction (B = xy^6 sigma(A)), every light boundary is a pair
of A-images: b = (A*f | monomial * sigma(A*sigma(f))), so |b| =
|A*f| + |A*(sigma f)|.  The building blocks are the low-weight elements of
V := im(A * -) = the S0-avoiding subspace (dim 71, min distance 3).

This script censuses V's low-weight layer exactly:
  1. weight-3 elements ("A-lines"): exhaustive over C(75,3) triples via
     the S0-character sum over GF(16); orbit structure under translation
     (are they all A-translates? — A itself is one);
  2. weight-4 elements: exhaustive over C(75,4) via meet-in-middle on the
     4-bit S0-syndrome (pairs with equal syndrome);
  3. weight-5: counted by the same collision method (pairs vs triples).

The S0-syndrome of a cell g is the GF(16) value chi(g) at the orbit-19
rep character (1,14); u in V iff its cells' syndromes XOR to 0 (the other
three orbit characters are Frobenius conjugates — one GF(16) equation).

Usage: uv run python scripts/a15_f2a6_athin_lines.py
"""

from __future__ import annotations

import itertools
import sys
from collections import Counter
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

A_STR = "1 + y + x"
ELL, M = 5, 15
Gb = AbelianGroup((ELL, M))
nb = Gb.cardinality
elems_b = list(Gb)
base_idx = {g: i for i, g in enumerate(Gb)}
Ab = Poly.from_string(A_STR, Gb)

# GF(16) tables (t^4 = t + 1)
def _mul(a: int, b: int) -> int:
    r = 0
    for k in range(4):
        if (b >> k) & 1:
            aa = a
            for _ in range(k):
                aa <<= 1
                if aa & 16:
                    aa ^= 0b10011
            r ^= aa
    return r & 15

T_POW = [1]
for _ in range(14):
    T_POW.append(_mul(T_POW[-1], 2))

# S0 = orbit of character (1, 14):  chi(i, j) = t^((3*i + 14*j) mod 15)
SYN = np.array([T_POW[(3 * i + 14 * j) % 15] for (i, j) in elems_b],
               dtype=np.uint8)
# sanity: A is in V (its syndrome XORs to 0)
sA = 0
for g in sorted(Ab.support):
    sA ^= SYN[base_idx[g]]
assert sA == 0, "A not S0-null?!"
print("sanity: A's S0-syndrome = 0  (A is an A-line)")

# ------------------------------------------------ 1. weight-3 elements
print("== weight-3 elements of V (exhaustive over C(75,3)) ==")
lines = []
syn_to_cells: dict[int, list[int]] = {}
for i in range(nb):
    syn_to_cells.setdefault(int(SYN[i]), []).append(i)
for i, j in itertools.combinations(range(nb), 2):
    s = int(SYN[i] ^ SYN[j])
    for k in syn_to_cells.get(s, []):
        if k > j:
            lines.append((i, j, k))
print(f"  weight-3 elements: {len(lines)}")
# translation-orbit census + how many are A-translates
def canon3(cells):
    pts = [elems_b[c] for c in cells]
    best = None
    for (cx, cy) in pts:
        t = tuple(sorted(((x - cx) % ELL, (y - cy) % M) for x, y in pts))
        best = t if best is None or t < best else best
    return best

orbit_census = Counter(canon3(c) for c in lines)
print(f"  translation classes: {len(orbit_census)} "
      f"(sizes {sorted(set(orbit_census.values()))})")
A_canon = canon3([base_idx[g] for g in Ab.support])
print(f"  A's class present: {A_canon in orbit_census}; "
      f"class reps: {sorted(orbit_census)[:6]}{' ...' if len(orbit_census) > 6 else ''}")

# ------------------------------------------------ 2. weight-4 elements
print("== weight-4 elements of V (meet-in-middle) ==")
pair_syn: dict[int, list[tuple[int, int]]] = {}
for i, j in itertools.combinations(range(nb), 2):
    pair_syn.setdefault(int(SYN[i] ^ SYN[j]), []).append((i, j))
n4 = 0
w4_classes = Counter()
for s, plist in pair_syn.items():
    for (i, j), (k, l) in itertools.combinations(plist, 2):
        if len({i, j, k, l}) == 4:
            n4 += 1
            w4_classes[canon3((i, j, k, l))] += 1  # canon3 works on any size
print(f"  weight-4 elements: {n4}; translation classes: {len(w4_classes)}")

# ------------------------------------------------ 3. weight-5 count
print("== weight-5 elements of V (collision count) ==")
n5 = 0
for i, j, k in lines:
    pass  # lines are weight-3; weight-5 = triple + pair with equal syndromes
# count: pairs (T, P) with syndrome(T) = syndrome(P), T weight-3 subset,
# P disjoint pair; syndrome(T) != 0 here (else T in V and P must be in V:
# no weight-2 in V).  Enumerate triples by syndrome.
triple_syn: dict[int, int] = Counter()
for i, j in itertools.combinations(range(nb), 2):
    s2 = int(SYN[i] ^ SYN[j])
    # third cell k > j to avoid dup; but for counting weight-5 we need all
    # triples; do full triple loop cheaply via syn_to_cells sizes instead
# full triple census by syndrome (75^3/6 ~ 68k — just loop)
tri_by_syn: dict[int, list[tuple[int, int, int]]] = {}
for tri in itertools.combinations(range(nb), 3):
    s = int(SYN[tri[0]] ^ SYN[tri[1]] ^ SYN[tri[2]])
    tri_by_syn.setdefault(s, []).append(tri)
for s, tris in tri_by_syn.items():
    if s == 0:
        continue
    for tri in tris:
        for (i, j) in pair_syn.get(s, []):
            if i not in tri and j not in tri:
                n5 += 1
n5 //= 1  # each weight-5 set counted once per (triple, pair) split: C(5,3)=10 splits... correct below
print(f"  raw (triple,pair) matches: {n5} — each weight-5 set counted "
      f"C(5,2)=10 times -> {n5 // 10} sets")

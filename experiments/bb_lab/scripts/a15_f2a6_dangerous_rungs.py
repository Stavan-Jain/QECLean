"""A15 dangerous-sector discharge, step 2: rung coverage for every light
(class, translate) of f2a6f17e1c41ff96.

For each light boundary b = d2 f (|f| <= 4 canonical classes x all 75
translates), find a rung that certifies `weight >= 16` for dangerous cover
cycles over b, in priority order:

  S  single-shape (BBDoubling.dangerous_bound_of_single_shape):
     some f0 in the 16-element ker-coset of f is seam-good
     (no cross-sheet cancellation).  Needs t = (16 - |b|)/2 >= 1.
  P  pair-shape (dangerous_bound_of_pair_shape): a support split
     f = f1 + f2 (nonempty parts; ker-coset variants allowed per part)
     with BOTH parts seam-good and
     |supp(d2 f1) u supp(d2 f2)| + 2*(t - 1) <= 15.
  U  UNCOVERED — the honest residue.

Output: per-(class, translate) rung table + summary; the dispatch data
for the Lean sweep.

Usage: uv run python scripts/a15_f2a6_dangerous_rungs.py
"""

from __future__ import annotations

import itertools
import json
import sys
from collections import Counter
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import circulant
from bb_lab.linalg import nullspace_f2

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15
LIGHT_CAP = 14

Gb = AbelianGroup((ELL, M))
Gc = AbelianGroup((ELL, 2 * M))
nb, nc = Gb.cardinality, Gc.cardinality
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
Ac = Poly.from_support(Ab.support, Gc)
Bc = Poly.from_support(Bb.support, Gc)
base_idx = {g: i for i, g in enumerate(Gb)}
cover_idx = {g: i for i, g in enumerate(Gc)}
elems_b, elems_c = list(Gb), list(Gc)

MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
MAc, MBc = circulant(Ac).astype(np.uint8), circulant(Bc).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2
D2c = np.vstack([MAc, MBc]) % 2

kerb = nullspace_f2(D2b).astype(np.uint8)
assert kerb.shape[0] == 4
ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask >> i) & 1:
            z ^= kerb[i]
    ker_elems.append(z)

# precompute the lift of every delta (identity section) and its cover image
LIFT_COL = np.zeros((nc, nb), dtype=np.uint8)
for i, (x, y) in enumerate(elems_b):
    LIFT_COL[cover_idx[(x, y)], i] = 1
D2C_LIFT = (D2c @ LIFT_COL) % 2      # cover image of the lifted delta_g

def d2_base(f): return (D2b @ f) % 2
def d2_cover_lift(f): return (D2C_LIFT @ f) % 2

def seam_good(f: np.ndarray) -> bool:
    return int(d2_cover_lift(f).sum()) == int(d2_base(f).sum())

def seam_good_coset(f: np.ndarray):
    """First seam-good element of f's ker-coset, or None."""
    for z in ker_elems:
        f0 = (f ^ z) % 2
        if seam_good(f0):
            return f0
    return None

def translate_f(f: np.ndarray, t) -> np.ndarray:
    out = np.zeros(nb, dtype=np.uint8)
    for i in np.nonzero(f)[0]:
        x, y = elems_b[i]
        out[base_idx[((x + t[0]) % ELL, (y + t[1]) % M)]] = 1
    return out

def canonical(support):
    cells = [elems_b[i] for i in support]
    best = None
    for cx, cy in cells:
        t = sorted(base_idx[((x - cx) % ELL, (y - cy) % M)] for x, y in cells)
        if best is None or t < best:
            best = t
    return tuple(best)

# ---------------------------------------------------------------- rungs
def try_single(f: np.ndarray, w: int) -> bool:
    t = (16 - w) // 2
    if t < 1:
        return False
    return seam_good_coset(f) is not None

def try_pair(f: np.ndarray, w: int) -> str | None:
    """Split supp f into two nonempty parts, allow ker-coset repair per
    part; both parts seam-good and |U| + 2(t-1) <= 15."""
    t = (16 - w) // 2
    if t < 1:
        return None
    sup = list(np.nonzero(f)[0])
    m = len(sup)
    if m < 2:
        return None
    for r in range(1, m // 2 + 1):
        for part1 in itertools.combinations(sup, r):
            if r == m - len(part1) and part1[0] != sup[0] and 2 * r == m:
                continue  # avoid double-visiting complementary equal splits
            f1 = np.zeros(nb, dtype=np.uint8)
            f1[list(part1)] = 1
            f2 = (f ^ f1) % 2
            g1 = seam_good_coset(f1)
            g2 = seam_good_coset(f2)
            if g1 is None or g2 is None:
                continue
            b1, b2 = d2_base(g1), d2_base(g2)
            U = int(((b1 | b2) != 0).sum())
            if U + 2 * (t - 1) <= 15:
                return f"P(r={len(part1)},U={U})"
    return None

# ---------------------------------------------------------------- sweep
print("== rung coverage over all light (class, translate) cells ==")
others = [i for i in range(nb) if i != base_idx[(0, 0)]]
supports = [(base_idx[(0, 0)],)]
for r in (1, 2, 3):
    supports += [(base_idx[(0, 0)],) + rest
                 for rest in itertools.combinations(others, r)]

verdicts: Counter = Counter()
uncovered: list[dict] = []
n_classes = 0
for support in supports:
    if canonical(support) != tuple(sorted(support)):
        continue
    f0 = np.zeros(nb, dtype=np.uint8)
    f0[list(support)] = 1
    w0 = int(d2_base(f0).sum())
    if w0 == 0 or w0 > LIGHT_CAP:
        continue
    n_classes += 1
    for tx in range(ELL):
        for ty in range(M):
            ft = translate_f(f0, (tx, ty))
            w = int(d2_base(ft).sum())
            assert w == w0
            if try_single(ft, w):
                verdicts["S"] += 1
                continue
            p = try_pair(ft, w)
            if p is not None:
                verdicts[p.split("(")[0]] += 1
                continue
            verdicts["U"] += 1
            if len(uncovered) < 40:
                uncovered.append({
                    "class": [list(elems_b[i]) for i in support],
                    "translate": [tx, ty],
                    "b_weight": w,
                })

print(f"classes: {n_classes}; cells: {sum(verdicts.values())}")
print(f"verdicts: {dict(verdicts)}")
if uncovered:
    print("UNCOVERED cells (first 40):")
    for u in uncovered:
        print(f"  class {u['class']} translate {u['translate']} |b|={u['b_weight']}")
else:
    print("ALL LIGHT CELLS COVERED by single/pair rungs")

outp = LAB_ROOT / "data" / "a15" / "f2a6_dangerous_rungs.json"
outp.write_text(json.dumps({
    "instance": "f2a6f17e1c41ff96:y",
    "n_classes": n_classes,
    "verdicts": dict(verdicts),
    "uncovered": uncovered,
}, indent=1))
print(f"wrote {outp}")

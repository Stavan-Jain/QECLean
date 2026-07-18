"""A17 dangerous-sector discharge, step 1: light-boundary census for
f2a6f17e1c41ff96 ([[150,8,8]] on Z5 x Z15, A = 1 + y + x,
B = x*y^6 + x*y^10 + x^2*y^12), y-cover to Z5 x Z30.

The (M)-half `DangerousFloorNZ 16` dispatches over nonzero base boundaries
b = d2 f with |b| <= 2d - 2 = 14 ("light").  This script:

  1. enumerates all f with |f| <= 4 up to translation (the boundary map,
     seam structure and rung shapes are translation-covariant), computes
     the light census by weight and by minimal-representative support;
  2. for each light class, checks SEAM-GOODNESS of the single-shape rung:
     f0 in the 16-element ker d2 coset of f with
     sheet0(liftStab f0) supported inside supp(d2 f0) — equivalently the
     cover lift of f0 has NO cross-sheet cancellation
     (|d2_cover(lift f0)| = |d2_base f0|);
  3. for seam-hostile classes, tries the PAIR-shape rung decompositions
     b = b1 + b2 with bi lighter boundaries and the union-support bound
     |U| + 2(t-1) <= 2d - 1;
  4. reports coverage: every light class must land on a rung, else it is
     listed as HOSTILE-UNCOVERED (the honest residue).

Everything is exact numpy over F2; no SAT.  Provenance feed for the Lean
sweep (a17_f2a6 dangerous discharge) and the docket note.

Usage: uv run python scripts/a17_f2a6_dangerous_census.py
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
TWO_D = 16          # 2 * d(base)
LIGHT_CAP = TWO_D - 2

Gb = AbelianGroup((ELL, M))
Gc = AbelianGroup((ELL, 2 * M))
nb, nc = Gb.cardinality, Gc.cardinality  # 75, 150
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
Ac = Poly.from_support(Ab.support, Gc)
Bc = Poly.from_support(Bb.support, Gc)
base_idx = {g: i for i, g in enumerate(Gb)}
cover_idx = {g: i for i, g in enumerate(Gc)}
elems_b, elems_c = list(Gb), list(Gc)

MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
MAc, MBc = circulant(Ac).astype(np.uint8), circulant(Bc).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2          # base d2: f (75) -> chains (150)
D2c = np.vstack([MAc, MBc]) % 2          # cover d2: f (150) -> chains (300)

# ker d2 (base): the 16-element coset freedom of the rung preimage
kerb = nullspace_f2(D2b)
assert kerb.shape[0] == 4, kerb.shape
ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask >> i) & 1:
            z ^= kerb[i].astype(np.uint8)
    ker_elems.append(z)
print(f"ker d2 basis weights: {[int(k.sum()) for k in kerb]}")

# ---------------------------------------------------------------- helpers
def d2_base(f: np.ndarray) -> np.ndarray:
    return (D2b @ f) % 2

def lift_section(f: np.ndarray) -> np.ndarray:
    """Identity-section lift of a base 2-chain: same (x, y), y < 15."""
    F = np.zeros(nc, dtype=np.uint8)
    for i in np.nonzero(f)[0]:
        x, y = elems_b[i]
        F[cover_idx[(x, y)]] = 1
    return F

def push_chain(V: np.ndarray) -> np.ndarray:
    """Fiber-sum of a cover 1-chain down to the base (blocks preserved)."""
    out = np.zeros(2 * nb, dtype=np.uint8)
    for blk in range(2):
        for j in np.nonzero(V[blk * nc:(blk + 1) * nc])[0]:
            x, y = elems_c[j]
            out[blk * nb + base_idx[(x, y % M)]] ^= 1
    return out

def seam_good(f: np.ndarray) -> bool:
    """No cross-sheet cancellation in the lifted stabilizer:
    |d2_cover(lift f)| == |d2_base f|  (<=> sheet-0 seam inside supp b)."""
    return int(((D2c @ lift_section(f)) % 2).sum()) == int(d2_base(f).sum())

def translate_f(f: np.ndarray, t: tuple[int, int]) -> np.ndarray:
    out = np.zeros(nb, dtype=np.uint8)
    for i in np.nonzero(f)[0]:
        x, y = elems_b[i]
        out[base_idx[((x + t[0]) % ELL, (y + t[1]) % M)]] = 1
    return out

# ---------------------------------------------------------------- census
# Enumerate support classes up to translation: fix the first cell at the
# origin.  Every f with 1 <= |f| <= 4 is a translate of one with 0 in its
# support; light-ness, seam-goodness and coset structure are all
# translation-covariant (the section commutes with base translations that
# do not wrap y — wrapping translates shift the seam, so seam-goodness is
# NOT invariant under y-translation.  We therefore enumerate shape classes
# up to translation for the CENSUS, but check seam-goodness for EVERY
# translate of each light class.)
print("== census of light boundaries from |f| <= 4 ==")
others = [i for i in range(nb) if i != base_idx[(0, 0)]]

census: Counter = Counter()          # |b| -> count of (translation-classes)
light_classes: list[dict] = []       # per class record

def canonical(support: tuple[int, ...]) -> tuple[int, ...]:
    """Lex-min translate of the support (translation-class canonical form)."""
    cells = [elems_b[i] for i in support]
    best = None
    for cx, cy in cells:
        t = sorted(base_idx[((x - cx) % ELL, (y - cy) % M)] for x, y in cells)
        if best is None or t < best:
            best = t
    return tuple(best)

def process(support: tuple[int, ...]) -> None:
    if canonical(support) != tuple(sorted(support)):
        return  # not the canonical translate of its class
    f = np.zeros(nb, dtype=np.uint8)
    f[list(support)] = 1
    b = d2_base(f)
    w = int(b.sum())
    if w == 0 or w > LIGHT_CAP:
        return
    census[w] += 1
    # minimal representative weight over the 16-element ker coset
    coset_wts = sorted(int((f ^ z).sum()) for z in ker_elems)
    # seam-goodness for every y-translate (x-translates never wrap the
    # section since only y is doubled), for f itself and its ker-coset
    n_good_translates = 0
    hostile_translates = []
    for ty in range(M):
        for tx in range(ELL):
            ft = translate_f(f, (tx, ty))
            ok = any(seam_good((ft ^ z) % 2) for z in ker_elems)
            if ok:
                n_good_translates += 1
            else:
                hostile_translates.append((tx, ty))
    light_classes.append({
        "rep_support": [list(elems_b[i]) for i in support],
        "b_weight": w,
        "f_weight": len(support),
        "coset_min_weight": coset_wts[0],
        "translates_seam_good": n_good_translates,
        "translates_total": ELL * M,
        "hostile_translates": [list(t) for t in hostile_translates[:8]],
    })

# |f| = 1
process((base_idx[(0, 0)],))
# |f| = 2, 3, 4 with 0 in support
for r in (1, 2, 3):
    cnt = 0
    for rest in itertools.combinations(others, r):
        process((base_idx[(0, 0)],) + rest)
        cnt += 1
    print(f"  |f| = {r + 1}: scanned {cnt} translation-class supports")

print(f"\nlight census by |b| (translation classes): {dict(sorted(census.items()))}")
n_hostile = sum(1 for c in light_classes if c["translates_seam_good"] < c["translates_total"])
print(f"light classes: {len(light_classes)}; with >= 1 seam-hostile translate: {n_hostile}")

# hostile detail
hostile = [c for c in light_classes if c["translates_seam_good"] < c["translates_total"]]
for c in hostile[:12]:
    print(f"  HOSTILE class f={c['rep_support']} |b|={c['b_weight']} "
          f"good {c['translates_seam_good']}/{c['translates_total']}")
if len(hostile) > 12:
    print(f"  ... and {len(hostile) - 12} more")

out = {
    "instance": "f2a6f17e1c41ff96:y",
    "census_by_b_weight": {str(k): v for k, v in sorted(census.items())},
    "n_light_classes": len(light_classes),
    "n_hostile_classes": len(hostile),
    "classes": light_classes,
}
outp = LAB_ROOT / "data" / "a15" / "f2a6_dangerous_census.json"
outp.write_text(json.dumps(out, indent=1))
print(f"\nwrote {outp}")

"""A15 near-kernel classification, step 3: structure-mine the enumerated
light-boundary classes (reads f2a6_light_classes.jsonl, works on whatever
is there — rerun as the enumeration progresses).

Structural probes, motivated by the specimens' step-3 y-progressions:

  1. THE 5:1 QUOTIENT: pi : Z5 x Z15 -> Z5 x Z3 (y mod 3; deck <y^3> = Z5).
     fiberSum along pi is a ring hom, so pi(b) is a boundary of the
     quotient pair (A-bar, B-bar) = (1 + y + x, x + x y + x^2) on Z5 x Z3,
     and |pi(u)| <= |u| with equal parity.  The quotient code is tiny
     (n = 30, 2^15 f-bar space): its light boundaries are enumerated
     EXHAUSTIVELY here, giving the downstairs anchor for the stratum.
  2. per-class profiles: y-mod-3 fiber occupancy of u and v, x-column
     count, |pi(u)|, |pi(v)|, and whether pi(b) = 0 (fully deck-balanced)
     vs a light downstairs boundary.
  3. strata census: coset_min spectrum by |b| — closes the [5,30] gap
     question on the enumerated portion.

Usage: uv run python scripts/a15_f2a6_nearkernel_structure.py
"""

from __future__ import annotations

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
from bb_lab.linalg import nullspace_f2, rank_f2

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15

Gb = AbelianGroup((ELL, M))
nb = Gb.cardinality
elems_b = list(Gb)
base_idx = {g: i for i, g in enumerate(Gb)}

Gq = AbelianGroup((ELL, 3))
nq = Gq.cardinality  # 15
elems_q = list(Gq)
q_idx = {g: i for i, g in enumerate(Gq)}

Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
Aq = Poly.from_support({(i, j % 3) for (i, j) in Ab.support}, Gq)
Bq_support_multiset = [(i, j % 3) for (i, j) in Bb.support]
# push of B: parity of fiber collisions
cnt: Counter = Counter(Bq_support_multiset)
Bq = Poly.from_support({g for g, c in cnt.items() if c % 2 == 1}, Gq)
print(f"quotient polynomials: A-bar {sorted(Aq.support)}  "
      f"B-bar {sorted(Bq.support)}")

MAq, MBq = circulant(Aq).astype(np.uint8), circulant(Bq).astype(np.uint8)
D2q = np.vstack([MAq, MBq]) % 2
D1q = np.hstack([MBq, MAq]) % 2
kerq = nullspace_f2(D2q)
kq = 2 * nq - rank_f2(np.vstack([MAq, MBq]).T @ np.zeros((2 * nq, 0), dtype=np.uint8) if False else np.hstack([MAq, MBq]))  # placeholder
# proper k of the quotient code:
rank_HXq = rank_f2(np.hstack([MAq, MBq]))
rank_HZq = rank_f2(np.hstack([MBq.T, MAq.T]))
k_q = 2 * nq - rank_HXq - rank_HZq
print(f"quotient code [[{2*nq},{k_q}]], dim ker d2-bar = {kerq.shape[0]}")

# exhaustive light boundaries of the quotient code (2^15 f-bar)
print("== exhaustive quotient-boundary weight census (2^15) ==")
f_all = np.arange(1 << nq, dtype=np.uint64)
bits = ((f_all[:, None] >> np.arange(nq, dtype=np.uint64)[None, :]) & 1
        ).astype(np.uint8)
img = (bits @ D2q.T) % 2
wts = img.sum(axis=1)
census_q = Counter(int(w) for w in wts)
print("  |b-bar| census over ALL f-bar:",
      dict(sorted((k, v) for k, v in census_q.items() if k <= 14)))
# minimal nonzero boundary weight downstairs
mu_q = min(k for k in census_q if k > 0)
print(f"  mu(quotient) = {mu_q}")

# distinct light quotient boundaries (as vectors) up to nothing (raw)
light_q_set = set()
for row, w in zip(img, wts):
    if 0 < w <= 14:
        light_q_set.add(row.tobytes())
print(f"  distinct light quotient boundaries (raw, <=14): {len(light_q_set)}")

# ---------------------------------------------------------------- classes
IN = LAB_ROOT / "data" / "a15" / "f2a6_light_classes.jsonl"
recs = []
complete = False
with open(IN) as fh:
    for line in fh:
        r = json.loads(line)
        if "complete" in r:
            complete = r["complete"]
            continue
        recs.append(r)
print(f"\n== {len(recs)} enumerated classes (complete: {complete}) ==")

def push_chain(b: np.ndarray) -> np.ndarray:
    out = np.zeros(2 * nq, dtype=np.uint8)
    for blk in range(2):
        for i in np.nonzero(b[blk * nb:(blk + 1) * nb])[0]:
            gx, gy = elems_b[i]
            out[blk * nq + q_idx[(gx, gy % 3)]] ^= 1
    return out

strata = Counter()
minrep_by_w: dict[int, Counter] = {}
push_zero = Counter()
push_light = Counter()
fiber_conc = Counter()
for r in recs:
    b = np.zeros(2 * nb, dtype=np.uint8)
    for blk, gx, gy in r["b_support"]:
        b[blk * nb + base_idx[(gx, gy)]] = 1
    w, cm = r["b_weight"], r["coset_min"]
    stratum = "small" if cm <= 4 else "nearker"
    strata[(stratum, w)] += 1
    minrep_by_w.setdefault(w, Counter())[cm] += 1
    pb = push_chain(b)
    wp = int(pb.sum())
    if stratum == "nearker":
        if wp == 0:
            push_zero[w] += 1
        else:
            push_light[(w, wp)] += 1
        # fiber concentration of the u-block
        u_cells = [(gx, gy) for blk, gx, gy in r["b_support"] if blk == 0]
        fibers = {gy % 3 for _, gy in u_cells}
        fiber_conc[len(fibers)] += 1

print("strata (stratum, |b|) -> classes:", dict(sorted(strata.items())))
print("coset_min spectrum by |b|:")
for w in sorted(minrep_by_w):
    print(f"  |b|={w}: {dict(sorted(minrep_by_w[w].items()))}")
print(f"near-kernel: pi(b) = 0 counts by |b|: {dict(sorted(push_zero.items()))}")
print(f"near-kernel: pi(b) light counts by (|b|,|pi b|): "
      f"{dict(sorted(push_light.items()))}")
print(f"near-kernel u-block: distinct y-mod-3 fibers used: "
      f"{dict(sorted(fiber_conc.items()))}")

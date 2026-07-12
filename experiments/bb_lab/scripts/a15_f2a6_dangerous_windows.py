"""A15 dangerous-sector discharge, step 3: window rung for the 115 cells
single/pair rungs miss (all |b| = 14, t = 1, seam-wrapping translates).

Window rung (to be added to BBDoubling as `dangerous_bound_of_window`):
for t = 1, a dangerous cycle v over b either has an off-cell
(|v| >= |b| + 2 = 16, done) or normalizes to tau(u) + liftStab f0 with

    u = sheet0(v) + seam(f0)  supported inside  W := supp(b) u seam(f0).

If EVERY base 1-cycle supported inside W is a boundary, then u is a
boundary and v is a boundary — contradiction.  So the per-cell finite
obligation is:  {cycles supported in W} = {boundaries supported in W},
checkable by rank over F2 (lab) / 2^|W| enumeration (Lean kernel).

This script: per uncovered cell, pick f0 in the ker-coset minimizing
|seam \ supp b| (poke count), report |W|, and check the window condition
two ways (rank identity + direct enumeration when |W| <= 24).

Usage: uv run python scripts/a15_f2a6_dangerous_windows.py
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
from bb_lab.checks import circulant
from bb_lab.linalg import nullspace_f2, rank_f2

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15

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
D1b = np.hstack([MBb, MAb]) % 2
D2c = np.vstack([MAc, MBc]) % 2

kerb = nullspace_f2(D2b).astype(np.uint8)
ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask >> i) & 1:
            z ^= kerb[i]
    ker_elems.append(z)

LIFT_COL = np.zeros((nc, nb), dtype=np.uint8)
for i, (x, y) in enumerate(elems_b):
    LIFT_COL[cover_idx[(x, y)], i] = 1
D2C_LIFT = (D2c @ LIFT_COL) % 2

def d2_base(f): return (D2b @ f) % 2

def seam_of(f: np.ndarray) -> np.ndarray:
    """sheet0 of the lifted stabilizer, in base coordinates."""
    L = (D2C_LIFT @ f) % 2
    s = np.zeros(2 * nb, dtype=np.uint8)
    for blk in range(2):
        for h in Gb:
            s[blk * nb + base_idx[h]] = L[blk * nc + cover_idx[(h[0], h[1])]]
    return s

def translate_f(f, t):
    out = np.zeros(nb, dtype=np.uint8)
    for i in np.nonzero(f)[0]:
        x, y = elems_b[i]
        out[base_idx[((x + t[0]) % ELL, (y + t[1]) % M)]] = 1
    return out

def window_ok_rank(W_mask: np.ndarray) -> bool:
    """{cycles in W} == {boundaries in W}, by rank identity."""
    idx = np.nonzero(W_mask)[0]
    # cycles in W: kernel of D1 restricted to columns W
    D1W = D1b[:, idx]
    dim_cyc = len(idx) - rank_f2(D1W.T)
    # boundaries in W: {D2 f : D2 f subset W} -> dim = dim ker(P_Wc . D2)
    # minus dim ker D2  (P_Wc = projection onto complement of W)
    cidx = np.nonzero(1 - W_mask)[0]
    D2out = D2b[cidx, :]
    dim_pre = nb - rank_f2(D2out.T)          # f with D2 f supported in W
    dim_bd = dim_pre - kerb.shape[0]         # minus ker D2 (dim 4)
    return dim_cyc == dim_bd

def window_ok_enum(W_mask: np.ndarray) -> bool:
    """Direct 2^|W| enumeration (mirrors the Lean-side check)."""
    idx = np.nonzero(W_mask)[0]
    w = len(idx)
    if w > 24:
        return window_ok_rank(W_mask)
    D1W = D1b[:, idx].astype(np.uint8)
    # all subsets: which are cycles
    exps = np.arange(w, dtype=np.uint64)
    n_cyc = 0
    CH = 1 << 16
    for start in range(0, 1 << w, CH):
        ids = np.arange(start, min(start + CH, 1 << w), dtype=np.uint64)
        bits = ((ids[:, None] >> exps[None, :]) & 1).astype(np.uint8)
        syn = (bits @ D1W.T) % 2
        n_cyc += int((syn.sum(axis=1) == 0).sum())
    # boundaries in W (count via rank)
    cidx = np.nonzero(1 - W_mask)[0]
    dim_pre = nb - rank_f2(D2b[cidx, :].T)
    n_bd = 1 << (dim_pre - kerb.shape[0])
    return n_cyc == n_bd

# ---------------------------------------------------------------- sweep
uncov = json.load(open(LAB_ROOT / "data" / "a15" / "f2a6_dangerous_rungs.json"))
cells = uncov["uncovered"]
print(f"uncovered cells from rung pass: {uncov['verdicts'].get('U', 0)} "
      f"(recorded {len(cells)}; re-deriving all)")

# re-derive the full uncovered list (the json capped at 40)
def canonical(support):
    cellsx = [elems_b[i] for i in support]
    best = None
    for cx, cy in cellsx:
        t = sorted(base_idx[((x - cx) % ELL, (y - cy) % M)] for x, y in cellsx)
        if best is None or t < best:
            best = t
    return tuple(best)

def seam_good(f):
    return int(((D2C_LIFT @ f) % 2).sum()) == int(d2_base(f).sum())

def seam_good_coset(f):
    for z in ker_elems:
        if seam_good((f ^ z) % 2):
            return (f ^ z) % 2
    return None

def try_pair(f, w):
    t = (16 - w) // 2
    sup = list(np.nonzero(f)[0])
    for r in range(1, len(sup) // 2 + 1):
        for part1 in itertools.combinations(sup, r):
            f1 = np.zeros(nb, dtype=np.uint8)
            f1[list(part1)] = 1
            f2 = (f ^ f1) % 2
            g1, g2 = seam_good_coset(f1), seam_good_coset(f2)
            if g1 is None or g2 is None:
                continue
            b1, b2 = d2_base(g1), d2_base(g2)
            if int(((b1 | b2) != 0).sum()) + 2 * (t - 1) <= 15:
                return True
    return False

others = [i for i in range(nb) if i != base_idx[(0, 0)]]
supports = [(base_idx[(0, 0)],)]
for r in (1, 2, 3):
    supports += [(base_idx[(0, 0)],) + rest
                 for rest in itertools.combinations(others, r)]

results = []
n_ok = 0
for support in supports:
    if canonical(support) != tuple(sorted(support)):
        continue
    f0 = np.zeros(nb, dtype=np.uint8)
    f0[list(support)] = 1
    w0 = int(d2_base(f0).sum())
    if w0 == 0 or w0 > 14:
        continue
    for tx in range(ELL):
        for ty in range(M):
            ft = translate_f(f0, (tx, ty))
            if seam_good_coset(ft) is not None:
                continue
            if try_pair(ft, w0):
                continue
            # window cell: best f0 = min-poke coset element
            b = d2_base(ft)
            best = None
            for z in ker_elems:
                fz = (ft ^ z) % 2
                s = seam_of(fz)
                poke = int((s & (1 - b)).sum())
                if best is None or poke < best[0]:
                    best = (poke, fz, s)
            poke, fz, s = best
            W = (b | s) % 2
            wsize = int(W.sum())
            ok_r = window_ok_rank(W)
            ok_e = window_ok_enum(W) if wsize <= 24 else None
            results.append({
                "class": [list(elems_b[i]) for i in support],
                "translate": [tx, ty],
                "b_weight": w0,
                "poke": poke,
                "window_size": wsize,
                "window_ok_rank": bool(ok_r),
                "window_ok_enum": (None if ok_e is None else bool(ok_e)),
            })
            if ok_r:
                n_ok += 1

print(f"window cells: {len(results)}; window condition holds: {n_ok}")
sizes = sorted(set(r["window_size"] for r in results))
print(f"window sizes: {sizes}")
bad = [r for r in results if not r["window_ok_rank"]]
for r in bad[:10]:
    print(f"  WINDOW FAILS: class {r['class']} t={r['translate']} |W|={r['window_size']}")
mismatch = [r for r in results
            if r["window_ok_enum"] is not None
            and r["window_ok_enum"] != r["window_ok_rank"]]
print(f"rank/enum mismatches: {len(mismatch)}")

outp = LAB_ROOT / "data" / "a15" / "f2a6_dangerous_windows.json"
outp.write_text(json.dumps({"cells": results}, indent=1))
print(f"wrote {outp}")

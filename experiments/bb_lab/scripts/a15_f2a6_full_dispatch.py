"""A15 near-kernel classification, step 6: the UNIFIED rung dispatch over
the complete light-boundary class list (small-preimage + near-kernel).

For every enumerated class x 75 translates, find a discharge route for
`DangerousFloorNZ 16` in priority order:

  S   single-shape rung: some preimage in the 16-element ker-coset is
      seam-good (no cross-sheet cancellation of the lifted stabilizer);
      works for any t = (16 - |b|)/2 >= 1.
  P   pair-shape rung: b = b1 + b2 with b1 (a translate of) an enumerated
      light class, b2 = b + b1 also light, both with seam-good preimages,
      and |supp b1 u supp b2| + 2(t-1) <= 15.  (Generalizes the census
      pair search: pieces need not come from support splits.)
  W   window rung (t = 1 only): every base cycle supported in
      supp b u seam(f0) is a boundary (2^|W| check; f0 = min-poke
      preimage).
  W+  generalized-window FEASIBILITY probe (t >= 2, not yet a Lean rung):
      every cycle in supp b u seam(f0) u E is a boundary for all extra
      cell sets |E| <= t - 1.  Reported as candidate route; the Lean
      side would need the rung generalization.
  U   uncovered — honest residue.

Outputs data/a15/f2a6_full_dispatch.json with per-class verdicts and the
poke statistics of near-kernel preimages (seam-crossing cancellations).

Usage: uv run python scripts/a15_f2a6_full_dispatch.py [--skip-wplus]
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import circulant
from bb_lab.linalg import nullspace_f2, rank_f2, rref_f2

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15

Gb = AbelianGroup((ELL, M))
Gc = AbelianGroup((ELL, 2 * M))
nb, nc = Gb.cardinality, Gc.cardinality
elems_b, elems_c = list(Gb), list(Gc)
base_idx = {g: i for i, g in enumerate(Gb)}
cover_idx = {g: i for i, g in enumerate(Gc)}
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
Ac = Poly.from_support(Ab.support, Gc)
Bc = Poly.from_support(Bb.support, Gc)
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


def solve_f2(Amat, b):
    aug = np.hstack([Amat.astype(np.uint8) % 2,
                     (b.astype(np.uint8) % 2)[:, None]])
    R, piv = rref_f2(aug)
    ncols = Amat.shape[1]
    if ncols in piv:
        return None
    x = np.zeros(ncols, dtype=np.uint8)
    for r, c in enumerate(piv):
        x[c] = R[r, ncols]
    return x


def seam_of(f):
    L = (D2C_LIFT @ f) % 2
    s = np.zeros(2 * nb, dtype=np.uint8)
    for blk in range(2):
        for h in elems_b:
            s[blk * nb + base_idx[h]] = L[blk * nc + cover_idx[(h[0], h[1])]]
    return s


def d2b(f):
    return (D2b @ f) % 2


def pokes(f):
    """Half the excess of the lifted image over the base image."""
    return (int(((D2C_LIFT @ f) % 2).sum()) - int(d2b(f).sum())) // 2


def seam_good_coset(f):
    for z in ker_elems:
        f0 = (f ^ z) % 2
        if pokes(f0) == 0:
            return f0
    return None


def min_poke_coset(f):
    best = None
    for z in ker_elems:
        f0 = (f ^ z) % 2
        p = pokes(f0)
        if best is None or p < best[0]:
            best = (p, f0)
    return best


TRANS = []
for tx in range(ELL):
    for ty in range(M):
        perm = np.zeros(2 * nb, dtype=np.int64)
        for i, (gx, gy) in enumerate(elems_b):
            j = base_idx[((gx + tx) % ELL, (gy + ty) % M)]
            perm[i] = j
            perm[nb + i] = nb + j
        TRANS.append(perm)


def translate_b(b, perm):
    out = np.zeros_like(b)
    out[perm] = b
    return out


def window_ok(W_mask, extra=()):
    Wm = W_mask.copy()
    for e in extra:
        Wm[e] = 1
    idx = np.nonzero(Wm)[0]
    D1W = D1b[:, idx]
    dim_cyc = len(idx) - rank_f2(D1W.T)
    cidx = np.nonzero(1 - Wm)[0]
    dim_pre = nb - rank_f2(D2b[cidx, :].T)
    return dim_cyc == dim_pre - kerb.shape[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-wplus", action="store_true")
    args = ap.parse_args()

    IN = LAB_ROOT / "data" / "a15" / "f2a6_light_classes.jsonl"
    recs, complete = [], False
    with open(IN) as fh:
        for line in fh:
            r = json.loads(line)
            if "complete" in r:
                complete = r["complete"]
            else:
                recs.append(r)
    print(f"{len(recs)} classes (enumeration complete: {complete})", flush=True)

    # all light b's (canonical + translates) for the pair search
    all_b = []
    for r in recs:
        b = np.zeros(2 * nb, dtype=np.uint8)
        for blk, gx, gy in r["b_support"]:
            b[blk * nb + base_idx[(gx, gy)]] = 1
        r["_b"] = b
        for perm in TRANS:
            all_b.append(translate_b(b, perm))
    b_bytes = {bb.tobytes(): bb for bb in all_b}
    print(f"light-b pool (with translates): {len(b_bytes)}", flush=True)

    # seam-good preimage per pool element (cache by bytes)
    sg_cache: dict[bytes, np.ndarray | None] = {}

    def pool_seam_good(bb):
        k = bb.tobytes()
        if k not in sg_cache:
            f = solve_f2(D2b, bb)
            sg_cache[k] = None if f is None else seam_good_coset(f)
        return sg_cache[k]

    verdicts = Counter()
    per_class = []
    t_start = time.time()
    for ci, r in enumerate(recs):
        w = r["b_weight"]
        t = (16 - w) // 2
        stratum = "small" if r["coset_min"] <= 4 else "nearker"
        row = {"class": ci, "stratum": stratum, "b_weight": w,
               "coset_min": r["coset_min"], "translates": {}}
        cell_verdicts = Counter()
        for perm in TRANS:
            tb = translate_b(r["_b"], perm)
            f = solve_f2(D2b, tb)
            assert f is not None
            # S
            if t >= 1 and seam_good_coset(f) is not None:
                cell_verdicts["S"] += 1
                continue
            # P: pieces from the pool
            covered = False
            if t >= 1:
                for bb in b_bytes.values():
                    b2 = (tb ^ bb) % 2
                    if not b2.any():
                        continue
                    k2 = b2.tobytes()
                    if k2 not in b_bytes:
                        continue
                    U = int(((bb | b2) != 0).sum())
                    if U + 2 * (t - 1) > 15:
                        continue
                    if pool_seam_good(bb) is None:
                        continue
                    if pool_seam_good(b2) is None:
                        continue
                    covered = True
                    break
            if covered:
                cell_verdicts["P"] += 1
                continue
            # W / W+
            p, f0 = min_poke_coset(f)
            W = (tb | seam_of(f0)) % 2
            wsize = int(W.sum())
            row.setdefault("poke_min", p)
            row["poke_min"] = min(row["poke_min"], p)
            if t == 1:
                if window_ok(W):
                    cell_verdicts["W"] += 1
                    continue
            elif not args.skip_wplus and wsize <= 30:
                ok = window_ok(W)
                if ok and t >= 2:
                    # probe: all single extra cells (t = 2 case exactly;
                    # for t = 3 this is only a necessary signal)
                    ok = all(window_ok(W, (e,))
                             for e in range(2 * nb) if not W[e])
                if ok:
                    cell_verdicts[f"W+(t={t})"] += 1
                    continue
            cell_verdicts["U"] += 1
        row["verdicts"] = dict(cell_verdicts)
        per_class.append(row)
        verdicts.update(cell_verdicts)
        if ci % 20 == 0 or stratum == "nearker":
            print(f"  class {ci} ({stratum}, |b|={w}): {dict(cell_verdicts)}"
                  f" [{time.time() - t_start:.0f} s]", flush=True)

    print(f"\nTOTAL verdicts: {dict(verdicts)}", flush=True)
    out = {"complete_enumeration": complete, "verdicts": dict(verdicts),
           "classes": per_class}
    (LAB_ROOT / "data" / "a15" / "f2a6_full_dispatch.json").write_text(
        json.dumps(out, indent=1))
    print("wrote data/a15/f2a6_full_dispatch.json", flush=True)


if __name__ == "__main__":
    main()

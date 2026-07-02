"""A11 S4 — the reachable-coset refinement of the safe floor.

The S2 matrix shows `safe_floor_ok` (all safe-class BASE coset minima
≥ 2d) is sufficient-shaped but not necessary: 41 doubling rows have a
safe class with base coset min < 2d (the "overlap-rescue" rows).  The
candidate repair: the base coset overcounts — a safe-sector cover
logical's projection p(v) lands in the *reachable* part of the class,

    reach(c) = (rep_c + rowspace(H_Z^base)) ∩ p(ker H_X^cover)
             = rep_c + (rowspace(H_Z^base) ∩ W),   W := p(cycle space),

so the honest per-class floor is min weight over reach(c), not over the
full coset.  |v| ≥ |p(v)| ≥ reach-min still holds, so

    C-safe' := tight witness ∧ every safe class reach-min ≥ 2d

is a sound safe-sector floor.  This script computes reach-minima for
matrix rows and answers two questions:

  1. do the 41 rescue rows have ALL reach-minima ≥ 2d?  (then C-safe'
     covers them — necessity repaired on this data);
  2. does any SHORT row have all reach-minima ≥ 2d?  (then C-safe' is
     NOT sufficient — the break would be dangerous-sector; count them).

Subspace intersection over F₂ via the kernel trick; coset-min via the
same dual-constraint SAT ladder as `a11_s3_diagnose.py`.  Everything
discovery/validation (A_HANDOFF §1).

Usage:
    uv run python scripts/a11_s4_reachable.py [--matrix data/a11/s2_matrix.jsonl]
                                              [--which rescue|short|all]
                                              [--limit N]
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2, rref_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import find_logical_z

from a9_lean_target_screen import blkdiag, cover_group, cover_maps, lift_poly, rowspace_basis
from a11_s3_diagnose import coset_min

OUT = LAB_ROOT / "data" / "a11" / "s4_reachable.jsonl"


def subspace_intersection(U: np.ndarray, W: np.ndarray) -> np.ndarray:
    """Row basis of rowspace(U) ∩ rowspace(W) over F₂."""
    if U.shape[0] == 0 or W.shape[0] == 0:
        return np.zeros((0, U.shape[1]), dtype=np.uint8)
    M = np.vstack([U, W]).T % 2  # n × (a+b); kernel = {(α,β): αU + βW = 0}
    ker = nullspace_f2(M)
    if ker.shape[0] == 0:
        return np.zeros((0, U.shape[1]), dtype=np.uint8)
    a = U.shape[0]
    vecs = (ker[:, :a] @ U) % 2
    return rowspace_basis(vecs)


def reachable_minima(rec: dict, cap: int) -> tuple[list[int | None], int]:
    Gb = AbelianGroup((rec["ell"], rec["m"]))
    A = Poly.from_string(rec["A"], Gb)
    B = Poly.from_string(rec["B"], Gb)
    axis = rec["axis"]
    ell, m = Gb.orders
    Gc = cover_group(ell, m, axis)
    chb = bb_check_matrices(A, B)
    chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
    HZb = chb.H_Z.astype(np.uint8)
    HXc = chc.H_X.astype(np.uint8)
    p_blk, _t, _s, _d = cover_maps(Gb, Gc, axis)
    P = blkdiag(p_blk)

    # W = p(cover cycle space); class reps from the logical-Z basis
    cyc = nullspace_f2(HXc)
    W = rowspace_basis((cyc @ P.T) % 2) if cyc.shape[0] else np.zeros((0, HZb.shape[1]), np.uint8)
    LZc = find_logical_z(chc)
    p_imgs = np.array([(P @ LZc[i]) % 2 for i in range(LZc.shape[0])], dtype=np.uint8)
    reps: list[np.ndarray] = []
    for i in range(p_imgs.shape[0]):
        stack = np.vstack([HZb] + ([np.array(reps)] if reps else []))
        if rank_f2(np.vstack([stack, p_imgs[i][None, :]])) > rank_f2(stack):
            reps.append(p_imgs[i])

    S_basis = rowspace_basis(HZb)
    I = subspace_intersection(S_basis, W)
    dual = nullspace_f2(I) if I.shape[0] else np.eye(HZb.shape[1], dtype=np.uint8)

    minima: list[int | None] = []
    r = len(reps)
    for mask in range(1, 1 << r):
        combo = np.zeros(HZb.shape[1], dtype=np.uint8)
        for i in range(r):
            if (mask >> i) & 1:
                combo ^= reps[i]
        minima.append(coset_min(combo, dual, cap))
    return minima, r


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--matrix", type=Path, default=LAB_ROOT / "data" / "a11" / "s2_matrix.jsonl")
    ap.add_argument("--which", choices=["rescue", "short", "all"], default="all")
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    rows = [json.loads(l) for l in args.matrix.open()]
    rows = [r for r in rows if r.get("error") is None and r.get("verdict") in ("DOUBLES", "short")]

    def is_rescue(r):
        return r["verdict"] == "DOUBLES" and not r["safe_floor_ok"]

    if args.which == "rescue":
        rows = [r for r in rows if is_rescue(r)]
    elif args.which == "short":
        rows = [r for r in rows if r["verdict"] == "short"]
    if args.limit:
        rows = rows[: args.limit]

    done: set[tuple[str, str]] = set()
    if OUT.exists():
        for line in OUT.open():
            r = json.loads(line)
            done.add((r["instance_id"], r["axis"]))

    n_rescue_ok = n_rescue = n_short_allheavy = n_short = 0
    t0 = time.time()
    with OUT.open("a") as fh:
        for rec in rows:
            key = (rec["instance_id"], rec["axis"])
            if key in done:
                continue
            cap = 2 * rec["d_base"] - 1
            minima, r = reachable_minima(rec, cap)
            all_heavy = all(mn is None for mn in minima)
            out = {k: rec[k] for k in ("instance_id", "group", "A", "B", "axis",
                                       "d_base", "d_cover", "verdict", "safe_floor_ok")}
            out["rank_p_star"] = r
            out["reach_minima"] = [(f">={cap+1}" if mn is None else mn) for mn in minima]
            out["reach_all_heavy"] = all_heavy
            fh.write(json.dumps(out) + "\n")
            fh.flush()
            if is_rescue(rec):
                n_rescue += 1
                n_rescue_ok += all_heavy
            if rec["verdict"] == "short":
                n_short += 1
                n_short_allheavy += all_heavy
            print(f"  {rec['group']}:{rec['axis']} {rec['verdict']:7s} "
                  f"floor_ok={rec['safe_floor_ok']} reach_all_heavy={all_heavy} "
                  f"minima={out['reach_minima']}", flush=True)
    print(f"\nrescue rows with reach all-heavy: {n_rescue_ok}/{n_rescue}")
    print(f"short rows with reach all-heavy (C-safe' sufficiency violations "
          f"unless dangerous-sector breaks exist): {n_short_allheavy}/{n_short}")
    print(f"({time.time()-t0:.0f}s) -> {OUT}")


if __name__ == "__main__":
    main()

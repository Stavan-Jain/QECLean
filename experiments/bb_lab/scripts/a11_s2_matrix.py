"""A11 S2 — the labeled feature matrix over the full A9 hunt stream.

For EVERY hunt candidate (the 152 doubling pairs AND the 465 failures and
21 k-drift rows the A9 profiler skipped), compute the no-cover-SAT feature
battery of `notes/A11_literal_lift_criterion.md` §4:

  - the A9 `profile_pair` block (dim ker ∂₂, μ(Ann), light-boundary census
    ≤ 2d−1, μ_Z, homotopy R = R2, linchpin, sq-ideal, safe-class coset
    minima, tight witness) — feasible on these frames (≤ 24 base cells);
  - the A11 certificate hierarchy (A8-exact / R0-sq / R0-univ-lin / R0 /
    sq2 / R1), parametric in the frame;
  - the difference-set predicates (D1/D2/D3, Frobenius gate) and the a5
    anchorability verdicts (i)/(ii)/(iii) on this presentation.

The `d_cover` label rides along from the hunt JSONL (SAT,
discovery/validation only — A_HANDOFF §1).

Usage:
    uv run python scripts/a11_s2_matrix.py [--jsonl data/a9/t1_hunt.jsonl]
                                           [--out data/a11/s2_matrix.jsonl]

Append-per-row and resumable: reruns skip (instance_id, axis) pairs already
in the output.
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

from bb_lab.checks import circulant
from bb_lab.diffset_predicates import (
    coordinate_separated,
    difference_sets_disjoint,
    is_frobenius_related,
    is_sidon,
)
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

from a5_cover_cascade import evaluate, is_anchorable
from a9_lean_target_screen import cover_group, lift_poly, profile_pair
from a11_s1_audit import solvable

DEFAULT_IN = LAB_ROOT / "data" / "a9" / "t1_hunt.jsonl"
DEFAULT_OUT = LAB_ROOT / "data" / "a11" / "s2_matrix.jsonl"


def certificate_features(A: Poly, B: Poly, Gb: AbelianGroup, axis: str) -> dict:
    """The A11 §1 hierarchy, parametric in the base frame."""
    ell, m = Gb.orders
    Gc = cover_group(ell, m, axis)
    Ac, Bc = lift_poly(A, Gc), lift_poly(B, Gc)
    deck = (ell, 0) if axis == "x" else (0, m)
    nc = Gc.cardinality
    target = np.zeros(nc, dtype=np.uint8)
    target[Gc.index((0, 0))] ^= 1
    target[Gc.index(deck)] ^= 1

    MAc = circulant(Ac).astype(np.uint8)
    MBc = circulant(Bc).astype(np.uint8)
    MAc2, MBc2 = (MAc @ MAc) % 2, (MBc @ MBc) % 2
    univ_idx = ([Gc.index((j, 0)) for j in range(Gc.orders[0])] if axis == "x"
                else [Gc.index((0, j)) for j in range(Gc.orders[1])])
    q_gross = np.zeros(nc, dtype=np.uint8)
    q_gross[Gc.index((0, 0))] ^= 1
    q_gross[Gc.index((2, 0) if axis == "x" else (0, 2))] ^= 1

    return {
        "A8exact_A": bool((((MAc2 @ q_gross) % 2) == target).all()),
        "A8exact_B": bool((((MBc2 @ q_gross) % 2) == target).all()),
        "R0sq_A": solvable(MAc2[:, univ_idx], target),
        "R0sq_B": solvable(MBc2[:, univ_idx], target),
        "R0lin_univ_A": solvable(MAc[:, univ_idx], target),
        "R0lin_univ_B": solvable(MBc[:, univ_idx], target),
        "R0_A": solvable(MAc, target),
        "R0_B": solvable(MBc, target),
        "sq2_A": solvable(MAc2, target),
        "sq2_B": solvable(MBc2, target),
        "R1": solvable(np.hstack([MAc, MBc]), target),
    }


def matrix_row(rec: dict) -> dict:
    Gb = AbelianGroup((rec["ell"], rec["m"]))
    A = Poly.from_string(rec["A"], Gb)
    B = Poly.from_string(rec["B"], Gb)
    axis = rec["axis"]

    row = {k: rec.get(k) for k in
           ("instance_id", "group", "ell", "m", "A", "B", "k", "d_base",
            "axis", "k_cover", "d_cover", "verdict")}
    row.update(certificate_features(A, B, Gb, axis))
    row["D1_sidon"] = bool(is_sidon(A) and is_sidon(B))
    row["D2_disjoint"] = bool(difference_sets_disjoint(A, B))
    row["D3_coord_sep"] = bool(coordinate_separated(A, B))
    row["frobenius"] = bool(is_frobenius_related(A, B))
    rep = evaluate("s2", Gb, A, B)
    row["anch_i"], row["anch_ii"], row["anch_iii"] = (
        rep.verdict_i, rep.verdict_ii, rep.verdict_iii)
    row["anchorable"] = is_anchorable(rep)
    row["frame_shape"] = rep.frame.shape

    # the A9 profiler block (census / safe minima / witness / R2 / linchpin)
    prof = profile_pair(rec)
    for k in ("base_cells", "dim_ker_d2", "mu_annA", "mu_annB", "mu_Z",
              "rank_d2", "boundary_census_le_2d_minus_1", "homotopy_R",
              "linchpin_imp_in_kertau", "sq_ideal_solvable", "sq_ideal_q1_zero",
              "rank_p_star", "safe_class_minima", "safe_floor_ok",
              "tight_witness"):
        row[k] = prof.get(k)
    return row


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jsonl", type=Path, default=DEFAULT_IN)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()

    recs = [json.loads(line) for line in args.jsonl.open()]
    done: set[tuple[str, str]] = set()
    if args.out.exists():
        for line in args.out.open():
            r = json.loads(line)
            done.add((r["instance_id"], r["axis"]))
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    n_new = 0
    with args.out.open("a") as fh:
        for i, rec in enumerate(recs):
            key = (rec["instance_id"], rec["axis"])
            if key in done:
                continue
            row = {"error": None}
            try:
                row = matrix_row(rec)
            except Exception as e:  # k_changed rows can break the profiler
                row = {k: rec.get(k) for k in
                       ("instance_id", "group", "ell", "m", "A", "B", "k",
                        "d_base", "axis", "k_cover", "d_cover", "verdict")}
                row["error"] = repr(e)
            fh.write(json.dumps(row, default=str) + "\n")
            fh.flush()
            n_new += 1
            if n_new % 25 == 0:
                print(f"  [{i+1}/{len(recs)}] +{n_new} rows, {time.time()-t0:.0f}s",
                      flush=True)
    print(f"done: +{n_new} rows in {time.time()-t0:.0f}s -> {args.out}", flush=True)


if __name__ == "__main__":
    main()

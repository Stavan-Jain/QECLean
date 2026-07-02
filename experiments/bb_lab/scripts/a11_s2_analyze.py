"""A11 S2 — analysis pass over the feature matrix.

Prints the necessity/sufficiency screen, the candidate-criterion
coverage table, and per-frame breakdowns from `data/a11/s2_matrix.jsonl`.
Pure reporting; no computation beyond counting.

Usage:
    uv run python scripts/a11_s2_analyze.py [--matrix PATH]
"""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent

FEATS = [
    "A8exact_A", "A8exact_B", "R0sq_A", "R0sq_B", "R0lin_univ_A",
    "R0lin_univ_B", "R0_A", "R0_B", "sq2_A", "sq2_B", "R1",
    "sq_ideal_solvable", "homotopy_R", "linchpin_imp_in_kertau",
    "safe_floor_ok", "tight_witness", "D1_sidon", "D2_disjoint",
    "D3_coord_sep", "frobenius", "anchorable", "anch_i", "anch_ii",
    "anch_iii",
]

CRITERIA = {
    "C-safe: R2 & linch & safe_floor & wit":
        lambda r: (r["homotopy_R"] and r["linchpin_imp_in_kertau"]
                   and r["safe_floor_ok"] and r["tight_witness"]),
    "safe_floor alone":
        lambda r: r["safe_floor_ok"],
    "wit alone":
        lambda r: r["tight_witness"],
    "A8exact (either side)":
        lambda r: r["A8exact_A"] or r["A8exact_B"],
    "R0sq (either side)":
        lambda r: r["R0sq_A"] or r["R0sq_B"],
}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--matrix", type=Path,
                    default=LAB_ROOT / "data" / "a11" / "s2_matrix.jsonl")
    args = ap.parse_args()

    rows = [json.loads(l) for l in args.matrix.open()]
    errs = [r for r in rows if r.get("error")]
    kdrift = [r for r in rows if r.get("verdict") == "k_changed"]
    usable = [r for r in rows if r.get("error") is None
              and r.get("verdict") in ("DOUBLES", "short")]
    D = [r for r in usable if r["verdict"] == "DOUBLES"]
    S = [r for r in usable if r["verdict"] == "short"]
    print(f"matrix: {len(rows)} rows = {len(D)} DOUBLES + {len(S)} short "
          f"+ {len(kdrift)} k_changed + {len(errs)} errors\n")

    print(f"{'feature':26s} {'P(f|DBL)':>9s} {'P(f|short)':>10s}  flags")
    for f in FEATS:
        pd = sum(1 for r in D if r.get(f)) / max(len(D), 1)
        ps = sum(1 for r in S if r.get(f)) / max(len(S), 1)
        flags = []
        if pd == 1.0:
            flags.append("NEC")
        if ps == 0.0 and pd > 0:
            flags.append("SUF")
        print(f"{f:26s} {pd:9.3f} {ps:10.3f}  {' '.join(flags)}")

    print()
    for name, pred in CRITERIA.items():
        tp = sum(1 for r in D if pred(r))
        fp = sum(1 for r in S if pred(r))
        print(f"{name:42s} covers {tp}/{len(D)} DOUBLES, "
              f"violations {fp}/{len(S)} shorts")

    print("\nper-frame DOUBLES coverage of C-safe:")
    by = collections.defaultdict(lambda: [0, 0])
    crit = CRITERIA["C-safe: R2 & linch & safe_floor & wit"]
    for r in D:
        key = f"{r['group']}:{r['axis']}"
        by[key][1] += 1
        if crit(r):
            by[key][0] += 1
    for key in sorted(by):
        c, t = by[key]
        print(f"  {key:12s} {c}/{t}")

    print("\nk-drift rows (recorded, excluded from analysis):",
          collections.Counter(r["group"] for r in kdrift))


if __name__ == "__main__":
    main()

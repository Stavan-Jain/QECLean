"""A10 — independent re-verification of the counterexample certificates.

For every row of `data/a10/s3_unrescued_certificates.jsonl` (and any
screen JSONL passed via --file): rebuild the cover from (base pair,
class, twist) alone, recompute k by rank, and for `fail` rows re-verify
the recorded witness — kernel membership, anticommutation with a
logical, non-membership in rowspan(H_X), and weight = recorded d ≤
2·d_base − 1 — using only numpy linear algebra (no SAT).  This is the
machine analogue of the Lean-kernel check the Fork-C packaging would
perform, and the lab's owed adversarial pass over the screen's output.

    uv run python scripts/a10_verify_certificates.py [--file PATH]
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.group import AbelianGroup
from bb_lab.linalg import rank_f2, nullspace_f2, quotient_complement_basis
from bb_lab.poly import Poly

from a10_descent_covers import descent_checks, code_k

DEFAULT = LAB_ROOT / "data" / "a10" / "s3_unrescued_certificates.jsonl"


def base_lookup() -> dict:
    import duckdb

    con = duckdb.connect(str(LAB_ROOT / "data" / "bb_instances.duckdb"), read_only=True)
    out = {
        r[0]: r
        for r in con.execute(
            "SELECT instance_id, ell, m, A_poly, B_poly, d_exact, k FROM bb_instances"
        ).fetchall()
    }
    con.close()
    return out


def verify_row(row: dict, meta) -> str:
    """Return '' if the row verifies, else a failure description."""
    _, ell, m, A_str, B_str, d_base, k_base = meta
    H = AbelianGroup((ell, m))
    A = Poly.from_string(A_str, H)
    B = Poly.from_string(B_str, H)
    checks, _ = descent_checks(
        A, B, tuple(row["cls"]), tuple(row["epsA"]), tuple(row["epsB"])
    )
    k = code_k(checks)
    if k != row["k"]:
        return f"k mismatch: recomputed {k} != recorded {row['k']}"
    v = row["verdict"]
    if v in ("k_zero", "k_drop"):
        return "" if k != k_base else "verdict says k-drop but k == k_base"
    if v == "fail":
        if k != k_base:
            return "verdict fail but k != k_base"
        if "witness" not in row:
            return "fail row without witness"
        w = np.zeros(checks.num_qubits, dtype=np.uint8)
        w[row["witness"]] = 1
        d_rec = row.get("d") or row.get("d_ub")
        if int(w.sum()) != d_rec:
            return f"witness weight {int(w.sum())} != recorded {d_rec}"
        if d_rec > 2 * d_base - 1:
            return f"recorded d {d_rec} not below 2*d_base"
        if ((checks.H_Z @ w) % 2).any():
            return "witness not in ker(H_Z)"
        ker_X = nullspace_f2(checks.H_X)
        L_Z = quotient_complement_basis(checks.H_Z, ker_X)
        if not ((L_Z @ w) % 2).any():
            return "witness commutes with all logical-Z reps"
        if rank_f2(np.vstack([checks.H_X, w])) == rank_f2(checks.H_X):
            return "witness lies in rowspan(H_X) (trivial logical)"
        return ""
    if v in ("rescue", "super"):
        return ""  # positives are certified separately (S5, LRAT)
    return f"unknown verdict {v}"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", type=Path, default=DEFAULT)
    args = ap.parse_args()
    meta = base_lookup()
    counts: Counter = Counter()
    failures = []
    rows = [json.loads(l) for l in open(args.file) if l.strip()]
    for i, row in enumerate(rows):
        err = verify_row(row, meta[row["base_id"]])
        counts[row["verdict"]] += 1
        if err:
            failures.append((i, row["base_id"], row["cls_name"], err))
        if (i + 1) % 500 == 0:
            print(f"  ... {i+1}/{len(rows)}", flush=True)
    print(f"verified {len(rows)} rows: {dict(counts)}")
    if failures:
        print(f"FAILURES ({len(failures)}):")
        for f in failures[:20]:
            print("  ", f)
        sys.exit(1)
    print("ALL ROWS VERIFY (independent numpy re-check; no SAT).")


if __name__ == "__main__":
    main()

"""A10 S3 — small-frame rescue-rate sweep.

For corpus bases on the direct-sweep frames (n_cover ≤ 96, weight-3
pairs, k > 0, d_exact ≥ 4), run the full 256-cover descent screen and
tabulate: does the base double literally (zero-twist axis covers)?  If
not, does SOME descent cover rescue it?  Turns the binary hit2/hit5
answer into a trend line (A10 plan §S3).

    uv run python scripts/a10_s3_rescue_sweep.py [--limit N] [--frames Z3xZ3,...]

Appends to data/a10/s3_smallframe_sweep.jsonl (resumable); writes the
per-base summary to data/a10/s3_summary.json.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

from a10_descent_covers import screen_base

FRAMES = ["Z3xZ3", "Z3xZ4", "Z3xZ5", "Z3xZ6", "Z4xZ6"]
OUT = LAB_ROOT / "data" / "a10" / "s3_smallframe_sweep.jsonl"
SUMMARY = LAB_ROOT / "data" / "a10" / "s3_summary.json"


def literal_rows(rows: list[dict]) -> dict[str, dict]:
    """The two zero-twist axis rows of one base's screen."""
    out = {}
    for r in rows:
        if all(e == 0 for e in r["epsA"]) and all(e == 0 for e in r["epsB"]):
            if r["cls_name"] in ("x", "y"):
                out[r["cls_name"]] = r
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--frames", default=",".join(FRAMES))
    args = ap.parse_args()
    frames = args.frames.split(",")

    import duckdb

    con = duckdb.connect(str(LAB_ROOT / "data" / "bb_instances.duckdb"), read_only=True)
    rows = con.execute(
        "SELECT instance_id, group_struct, ell, m, A_poly, B_poly, k, d_exact "
        "FROM bb_instances WHERE group_struct IN ("
        + ",".join("?" * len(frames))
        + ") AND k > 0 AND d_exact >= 4 AND A_weight = 3 AND B_weight = 3 "
        "ORDER BY group_struct, instance_id",
        frames,
    ).fetchall()
    con.close()
    if args.limit:
        rows = rows[: args.limit]
    print(f"S3 sweep: {len(rows)} bases on {frames}")

    summary = []
    t0 = time.time()
    for i, (iid, gs, ell, m, A_str, B_str, k, d) in enumerate(rows):
        H = AbelianGroup((ell, m))
        A = Poly.from_string(A_str, H)
        B = Poly.from_string(B_str, H)
        res = screen_base(iid, A, B, d, k, OUT)
        lit = literal_rows(res)
        rescues = [r for r in res if r["verdict"] == "rescue"]
        supers = [r for r in res if r["verdict"] == "super"]
        entry = {
            "instance_id": iid,
            "frame": gs,
            "k": k,
            "d_base": d,
            "literal_x": lit.get("x", {}).get("verdict"),
            "literal_y": lit.get("y", {}).get("verdict"),
            "literal_doubles": any(
                lit.get(a, {}).get("verdict") == "rescue" for a in ("x", "y")
            ),
            "n_rescue": len(rescues),
            "n_super": len(supers),
            "rescue_classes": sorted({r["cls_name"] for r in rescues}),
            "rescued": bool(rescues) or bool(supers),
        }
        summary.append(entry)
        print(
            f"[{i+1}/{len(rows)}] {gs} {iid} d={d} "
            f"literal={'YES' if entry['literal_doubles'] else 'no'} "
            f"rescues={len(rescues)} classes={entry['rescue_classes']} "
            f"({time.time()-t0:.0f}s)",
            flush=True,
        )

    SUMMARY.write_text(json.dumps(summary, indent=2))
    lit_fail = [e for e in summary if not e["literal_doubles"]]
    lit_fail_rescued = [e for e in lit_fail if e["rescued"]]
    print(
        f"\nbases: {len(summary)}; literal-doubling: "
        f"{sum(e['literal_doubles'] for e in summary)}; "
        f"literal-failures: {len(lit_fail)}; of those rescued by a twist: "
        f"{len(lit_fail_rescued)}"
    )
    for e in lit_fail:
        print(
            f"  {e['frame']} {e['instance_id']} d={e['d_base']} "
            f"rescued={'YES ' + ','.join(e['rescue_classes']) if e['rescued'] else 'NO'}"
        )
    print(f"wrote {SUMMARY}")


if __name__ == "__main__":
    main()

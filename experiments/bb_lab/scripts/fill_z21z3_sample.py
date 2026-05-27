"""SAT-fill d_exact for Z21xZ3 corpus rows.

The CLI `bb-lab fill-distances` walks (n, k)-order globally, so at n=126
it would hit ~12k Z9xZ6 rows first before reaching Z21xZ3 (n=126). This
script bypasses that by filtering directly on group_struct.

Default is parallel-8 via multiprocessing.Pool with the driver
serializing DB writes (DuckDB single-writer discipline). Pass --serial
for the simple in-process loop.

Usage:
  cd experiments/bb_lab
  uv run python scripts/fill_z21z3_sample.py 20            # 20 instances, parallel-8
  uv run python scripts/fill_z21z3_sample.py 200           # finish the regime
  uv run python scripts/fill_z21z3_sample.py 20 --serial   # serial fallback
"""

from __future__ import annotations

import argparse
import multiprocessing as mp
import os
import time

from bb_lab.checks import bb_check_matrices
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance
from bb_lab.store import DEFAULT_DB, connect


def _solve_one(args):
    """Worker: parse polys, run SAT, return (iid, distance, wall_time)."""
    iid, ell, m_, A_str, B_str = args
    G = ZmZn(ell, m_)
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    checks = bb_check_matrices(A, B)
    t = time.time()
    res = x_distance(checks, code_id=iid)
    return iid, res.distance, time.time() - t


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("limit", type=int, help="how many rows to fill")
    ap.add_argument("--group", default="Z21xZ3",
                    help="group_struct to target (default Z21xZ3)")
    ap.add_argument("--workers", type=int, default=0,
                    help="0 = auto (cpu_count, cap 8); 1 = serial.")
    ap.add_argument("--serial", action="store_true", help="alias for --workers 1")
    args = ap.parse_args()
    n_workers = 1 if args.serial else (args.workers or min(os.cpu_count() or 1, 8))

    with connect(DEFAULT_DB) as con:
        rows = con.execute(
            """SELECT instance_id, ell, m, A_poly, B_poly, n, k
                 FROM bb_instances
                WHERE group_struct = ?
                  AND d_exact IS NULL
                  AND k >= 2
                ORDER BY n, k
                LIMIT ?""",
            [args.group, args.limit],
        ).fetchall()
        if not rows:
            print(f"no pending {args.group} rows.")
            return

        mode = "serial" if n_workers == 1 else f"parallel-{n_workers}"
        ns = sorted({r[5] for r in rows})
        print(f"pending: {len(rows)} {args.group} rows (n∈{ns}) [{mode}]")
        t0 = time.time()
        wall_times: list[float] = []
        worker_inputs = [(iid, ell, m_, A_str, B_str)
                         for iid, ell, m_, A_str, B_str, _n, _k in rows]

        if n_workers == 1:
            it = (_solve_one(w) for w in worker_inputs)
        else:
            ctx = mp.get_context("spawn")
            pool = ctx.Pool(processes=n_workers)
            it = pool.imap_unordered(_solve_one, worker_inputs)

        try:
            for i, (iid, distance, dt) in enumerate(it, start=1):
                wall_times.append(dt)
                con.execute(
                    "UPDATE bb_instances SET d_exact = ?, d_method = 'sat', "
                    "updated_at = now() WHERE instance_id = ?",
                    [distance, iid],
                )
                print(f"  [{i:3d}/{len(rows)}] d={distance:2d}  ({dt:6.2f}s)")
        finally:
            if n_workers != 1:
                pool.close()
                pool.join()

    if wall_times:
        elapsed = time.time() - t0
        total_cpu = sum(wall_times)
        print()
        print(f"Wall-clock elapsed:    {elapsed:.1f}s")
        print(f"Sum of SAT wall:       {total_cpu:.1f}s")
        print(f"Mean per instance:     {total_cpu/len(wall_times):.2f}s")
        print(f"Max per instance:      {max(wall_times):.2f}s")


if __name__ == "__main__":
    main()

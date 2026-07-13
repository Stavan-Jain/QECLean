"""A16 — parallel L1-sampling distance upper bounds for corpus rows.

Parallel version of `bb-lab fill-distance-ubs`: worker processes run
`l1_distance_ub`, the driver serialises the DuckDB writes. Selection
defaults to rows with no d_ub and no d_exact.

Usage:
  uv run python a16_fill_ubs.py --db data/bb_instances.duckdb \
      [--min-n 0] [--max-n 10000] [--n-samples 30000] [--workers 8] \
      [--like 'bb_%']
"""

from __future__ import annotations

import argparse
import multiprocessing as mp
import time

from bb_lab.store import connect


def _ub_worker(job: tuple) -> tuple[str, int]:
    iid, ell, m, A_str, B_str, n_samples, seed = job
    from bb_lab.checks import bb_check_matrices
    from bb_lab.group import ZmZn
    from bb_lab.l1_sampling import l1_distance_ub
    from bb_lab.poly import Poly

    G = ZmZn(ell, m)
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    checks = bb_check_matrices(A, B)
    res = l1_distance_ub(checks, n_samples=n_samples, seed=seed)
    return iid, int(res.distance_ub)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", required=True)
    ap.add_argument("--min-n", type=int, default=0)
    ap.add_argument("--max-n", type=int, default=10_000)
    ap.add_argument("--n-samples", type=int, default=30_000)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--like", default="%", help="code_id LIKE filter")
    args = ap.parse_args()

    with connect(args.db) as con:
        rows = con.execute(
            """
            SELECT instance_id, ell, m, A_poly, B_poly
              FROM bb_instances
             WHERE d_ub IS NULL AND d_exact IS NULL AND k >= 2
               AND n BETWEEN ? AND ?
               AND code_id LIKE ?
             ORDER BY n, k
            """,
            [args.min_n, args.max_n, args.like],
        ).fetchall()
        print(f"pending d_ub: {len(rows)} rows", flush=True)
        jobs = [
            (iid, ell, m, A_str, B_str, args.n_samples, args.seed)
            for iid, ell, m, A_str, B_str in rows
        ]
        t0 = time.time()
        n_done = 0
        ctx = mp.get_context("spawn")
        with ctx.Pool(processes=args.workers) as pool:
            for iid, ub in pool.imap_unordered(_ub_worker, jobs, chunksize=16):
                con.execute(
                    "UPDATE bb_instances SET d_ub = ?, updated_at = now() "
                    "WHERE instance_id = ?",
                    [ub, iid],
                )
                n_done += 1
                if n_done % 2000 == 0:
                    dt = time.time() - t0
                    print(
                        f"  {n_done}/{len(jobs)}  ({dt:.0f}s, "
                        f"{n_done / dt:.0f}/s)",
                        flush=True,
                    )
        print(f"done: {n_done} d_ub values in {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()

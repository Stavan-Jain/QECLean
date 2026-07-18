"""A18 — flexible SAT exact-distance filler for the corpus DB.

Generalizes `bb-lab fill-distances`: arbitrary SQL row selection and
ordering, per-instance hard timeout (subprocess kill), N concurrent
single-solve workers, and a global wall-clock box so a pass can be
time-budgeted. All DB writes stay on the driver (DuckDB single writer).

Typical passes:
  # breadth-first over new small groups
  uv run python a18_sat_fill.py --db data/bb_instances.duckdb \
      --where "d_exact IS NULL AND n <= 100 AND k >= 2" \
      --breadth-first --timeout 60 --workers 8 --max-seconds 4200

  # d>=10 hunt in the 104..200 window, cheapest promising rows first
  uv run python a18_sat_fill.py --db data/bb_instances.duckdb \
      --where "d_exact IS NULL AND n BETWEEN 104 AND 200 AND d_ub >= 10" \
      --order "n ASC, d_ub ASC, k DESC" --timeout 300 --workers 8
"""

from __future__ import annotations

import argparse
import multiprocessing as mp
import time

from bb_lab.cli import _build_checks_for_row, _sat_d_worker
from bb_lab.store import connect

D_METHOD = "sat-cadical@1.9.5 (pysat)"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", required=True)
    ap.add_argument("--where", default="d_exact IS NULL AND k >= 2")
    ap.add_argument(
        "--order",
        default="n ASC, k DESC",
        help="ORDER BY expression (ignored with --breadth-first)",
    )
    ap.add_argument(
        "--breadth-first",
        action="store_true",
        help="round-robin across group_structs (each group's i-th row "
        "solves before any group's (i+1)-th)",
    )
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--max-seconds", type=float, default=None, help="global box")
    args = ap.parse_args()

    if args.breadth_first:
        order_sql = (
            "ROW_NUMBER() OVER (PARTITION BY group_struct ORDER BY n, k DESC), n"
        )
    else:
        order_sql = args.order

    sql = (
        "SELECT instance_id, group_struct, ell, m, A_poly, B_poly, n, k "
        f"FROM bb_instances WHERE {args.where} ORDER BY {order_sql}"
    )

    t_global = time.time()
    with connect(args.db) as con:
        rows = con.execute(sql).fetchall()
        if args.limit is not None:
            rows = rows[: args.limit]
        print(f"selected {len(rows)} rows  (timeout {args.timeout}s x {args.workers} workers)", flush=True)

        ctx = mp.get_context("spawn")
        row_iter = iter(rows)
        in_flight: dict[int, tuple] = {}
        next_slot = 0
        n_done = n_timeout = n_err = n_finished = 0
        d_hist: dict[int, int] = {}
        stop_submitting = False

        def spawn_next() -> bool:
            nonlocal next_slot, stop_submitting
            if stop_submitting:
                return False
            if args.max_seconds is not None and time.time() - t_global > args.max_seconds:
                stop_submitting = True
                print("  [global time box hit — draining in-flight]", flush=True)
                return False
            try:
                row = next(row_iter)
            except StopIteration:
                return False
            iid, gstruct, ell, m_, A_str, B_str, n_q, k_q = row
            checks = _build_checks_for_row(ell, m_, A_str, B_str)
            pool = ctx.Pool(processes=1)
            res = pool.apply_async(_sat_d_worker, (checks.H_X, checks.H_Z))
            in_flight[next_slot] = (iid, gstruct, n_q, k_q, pool, res, time.time())
            next_slot += 1
            return True

        for _ in range(args.workers):
            if not spawn_next():
                break

        while in_flight:
            now = time.time()
            done_slots = []
            for slot, (iid, gstruct, n_q, k_q, pool, res, t0) in in_flight.items():
                if res.ready():
                    dt = now - t0
                    try:
                        d = res.get(timeout=0)
                        con.execute(
                            "UPDATE bb_instances SET d_exact = ?, d_method = ?, "
                            "updated_at = now() WHERE instance_id = ?",
                            [d, D_METHOD, iid],
                        )
                        n_done += 1
                        d_hist[d] = d_hist.get(d, 0) + 1
                        if d >= 10 or n_done % 200 == 0:
                            print(
                                f"  {'**' if d >= 10 else 'OK'} [[{n_q},{k_q},{d}]] "
                                f"G={gstruct} ({dt:5.1f}s) [{n_finished + 1}/{len(rows)}]",
                                flush=True,
                            )
                    except Exception as exc:
                        con.execute(
                            "UPDATE bb_instances SET d_method = ?, updated_at = now() "
                            "WHERE instance_id = ?",
                            [f"sat-error: {type(exc).__name__}", iid],
                        )
                        n_err += 1
                        print(f"  ERROR [[{n_q},{k_q}]] G={gstruct} {type(exc).__name__}", flush=True)
                    pool.close()
                    pool.join()
                    n_finished += 1
                    done_slots.append(slot)
                elif now - t0 > args.timeout:
                    pool.terminate()
                    pool.join()
                    con.execute(
                        "UPDATE bb_instances SET d_method = ?, updated_at = now() "
                        "WHERE instance_id = ?",
                        [f"sat-timeout@{args.timeout}s", iid],
                    )
                    n_timeout += 1
                    n_finished += 1
                    print(
                        f"  TIMEOUT [[{n_q},{k_q}]] G={gstruct} "
                        f"[{n_finished}/{len(rows)}]",
                        flush=True,
                    )
                    done_slots.append(slot)
            for slot in done_slots:
                del in_flight[slot]
                spawn_next()
            if not done_slots and in_flight:
                time.sleep(0.05)

        dt = time.time() - t_global
        print(
            f"\nPASS DONE in {dt:.0f}s: {n_done} solved, {n_timeout} timeouts, "
            f"{n_err} errors",
            flush=True,
        )
        print("d histogram:", dict(sorted(d_hist.items())), flush=True)


if __name__ == "__main__":
    main()

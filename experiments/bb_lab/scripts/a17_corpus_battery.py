"""A17 Phase 1: the in-corpus d>=7 doubling battery.

A14 SS16 closed the literal-lift d > 12 hunt over *stored corpus
presentations of the Bravyi-table codes* and left "fresh-base
enumeration (d >= 7, k > 0)" as the constructive residue. The 2026-07-06
census (notes/A17_d7plus_doubling_hunt_plan.md SS0) found that pool
already sitting in `data/bb_instances.duckdb`, unscreened: 1,361
SAT-certified d >= 7, k > 0 rows the A14 battery never saw (the T1
screen corpus caps at d_base = 6; SS14 covered only bb_90/bb_108).

This driver runs the A14 battery over every such (row, axis) cell:

    k-gate (condition 2, A12 Bezout)  ->  S0/S1+/S2 cheap tiers
    ->  S4 per-G-orbit-rep coset SAT at floor 2*d_base on survivors
    ->  on SF-CERTIFIED: the exact cover distance ladder (payoff run).

Differences from `a14_d10_battery.py` (which it otherwise mirrors —
same tier semantics, same S4 orbit-rep protocol):

  * targets come from the corpus DuckDB (read-only), stratified
    d = 12 -> 10 -> 8, both axes per row;
  * S4 SAT witnesses are PERSISTED (support + weight), per the A17 plan
    — refutation witnesses are the Phase-3 deficit-wall dataset;
  * per-class cheap-tier weights are persisted (raw/s1p/s2/s2p), not
    just the row minimum, for the same reason;
  * `ODD_FACTORS` is extended with the x^21 - 1 factorization over F2
    (verified at import) — the corpus pool includes Z21xZ3 frames whose
    S2 blocks need it;
  * incremental JSONL output with resume (skip already-done cells), so
    the multi-hour d=8 stratum can run in the background and restart.

Screens are evaluated on the STORED presentation (A14 SS8 discipline: no
Aut-orbit maximization before screening; only G-translation symmetry is
used, inside S4's orbit reps). A CHEAP-REJECT or SF-REFUTED verdict is a
genuine coset element below the floor for THIS presentation; per-code
ceilings need an orbit sweep (SS15 protocol) and are out of scope here.

Run from `experiments/bb_lab/` (see --help):
    uv run python scripts/a17_corpus_battery.py --validate
    uv run python scripts/a17_corpus_battery.py --strata 12
    uv run python scripts/a17_corpus_battery.py --strata 8,10 --out data/a17/corpus_battery.jsonl
    uv run python scripts/a17_corpus_battery.py --summarize
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import a14_phase2_screens as p2  # noqa: E402
from a14_phase2_screens import screen_row_phase2  # noqa: E402
from a14_s4_ladder import orbit_reps  # noqa: E402
from a14_safe_floor_screens import (  # noqa: E402
    XCover, canonical_row, h1_dim, parse_poly)
from bb_lab.corpus import Corpus  # noqa: E402
from bb_lab.linalg import nullspace_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "data/a17/corpus_battery.jsonl"

# ------------------------------------------------- x^21 - 1 over F2 (for S2)
# x^21+1 = (x+1)(x^2+x+1)(x^3+x+1)(x^3+x^2+1)
#          (x^6+x^4+x^2+x+1)(x^6+x^5+x^4+x^2+1)
# Needed by block_idempotent_supports on the Z21xZ3 / Z3xZ21 frames.
_PHI21_FACTORS = [0b11, 0b111, 0b1011, 0b1101, 0b1010111, 0b1110101]
_prod = 1
for _f in _PHI21_FACTORS:
    _prod = p2.pmul(_prod, _f)
assert _prod == (1 << 21) | 1, "x^21 - 1 factor table is wrong"
for _i in range(len(_PHI21_FACTORS)):
    for _j in range(_i + 1, len(_PHI21_FACTORS)):
        _g, _, _ = p2.pegcd(_PHI21_FACTORS[_i], _PHI21_FACTORS[_j])
        assert _g == 1, "x^21 - 1 factors are not pairwise coprime"
p2.ODD_FACTORS[21] = _PHI21_FACTORS


# ----------------------------------------------------- S4 with witness dump


def coset_query_w(cov: XCover, seam: np.ndarray, w: int,
                  conf_budget: int = 3_000_000):
    """`a14_s4_ladder.coset_query`, plus the witness support on SAT.

    Returns (verdict, weight | None, support | None) where support is the
    sorted index list of the extracted coset element (a genuine element of
    seam + im d2 of the returned weight, kernel-checkable downstream).
    """
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    from pysat.solvers import Cadical153

    nb = cov.nb
    pool = IDPool()
    fvar = [pool.id(("f", j)) for j in range(nb)]
    cvar = [pool.id(("c", i)) for i in range(2 * nb)]
    clauses = []

    def xor_pair(a: int, b: int) -> int:
        t = pool.id(("x", a, b))
        clauses.extend([[-t, a, b], [-t, -a, -b], [t, -a, b], [t, a, -b]])
        return t

    for i in range(2 * nb):
        sup = np.flatnonzero(cov.d2b[i]).tolist()
        cur = None
        for j in sup:
            cur = fvar[j] if cur is None else xor_pair(cur, fvar[j])
        target = cvar[i]
        if cur is None:
            clauses.append([target] if seam[i] else [-target])
            continue
        if seam[i]:
            clauses.extend([[target, cur], [-target, -cur]])
        else:
            clauses.extend([[-target, cur], [target, -cur]])

    card = CardEnc.atmost(lits=cvar, bound=w, vpool=pool,
                          encoding=EncType.seqcounter)
    with Cadical153(bootstrap_with=clauses + card.clauses) as solver:
        solver.conf_budget(conf_budget)
        res = solver.solve_limited()
        if res is None:
            return "UNKNOWN", None, None
        if not res:
            return "UNSAT", None, None
        model = set(solver.get_model())
        f = np.array([1 if fvar[j] in model else 0 for j in range(nb)],
                     dtype=np.uint8)
        elem = seam ^ ((cov.d2b @ f) & 1)
        wt = int(elem.sum())
        assert wt <= w, "extracted certificate exceeds the bound"
        return "SAT", wt, np.flatnonzero(elem).tolist()


def s4_run(A, B, l, m, axis, d_base, conf_budget):
    """Orbit-rep S4 at floor 2*d_base; persists witnesses (A17 addition)."""
    Ac, Bc, lc, mc = canonical_row(A, B, l, m, axis)
    cov = XCover(Ac, Bc, lc, mc)
    ker = nullspace_f2(cov.d2b)
    reps = orbit_reps(cov, ker)
    floor = 2 * d_base
    verdicts = []
    for i, z in enumerate(reps):
        v, wt, sup = coset_query_w(cov, cov.seam(z), floor - 1, conf_budget)
        rec = {"rep": i, "verdict": v}
        if wt is not None:
            rec["weight"] = wt
            rec["witness_support"] = sup
        verdicts.append(rec)
        if v == "SAT":
            break  # one light class refutes SF
    status = ("SF-REFUTED" if any(r["verdict"] == "SAT" for r in verdicts)
              else "SF-CERTIFIED" if all(r["verdict"] == "UNSAT"
                                         for r in verdicts)
              else "INCONCLUSIVE")
    return {"floor": floor, "n_orbit_reps": len(reps),
            "verdicts": verdicts, "status": status}


def cover_distance_ladder(A_str, B_str, l, m, axis, ub):
    """Exact cover d_X on SF-CERTIFIED cells (every UNSAT step lb=2)."""
    from bb_lab.checks import bb_check_matrices
    from bb_lab.group import AbelianGroup
    from bb_lab.poly import Poly
    from bb_lab.sat_distance import x_distance
    dims = (2 * l, m) if axis == "x" else (l, 2 * m)
    G = AbelianGroup(dims)
    checks = bb_check_matrices(Poly.from_string(A_str, G),
                               Poly.from_string(B_str, G))
    try:
        res = x_distance(checks, weight_lower_bound=2, weight_upper_bound=ub,
                         verbose=False)
        return {"d_X": int(res.distance)}
    except RuntimeError:
        return {"d_X_lower": ub + 1}


# ------------------------------------------------------------ cell pipeline


def process_cell(row: dict, axis: str, conf_budget: int, run_s4: bool,
                 run_ladder: bool) -> dict:
    t0 = time.time()
    A, B = parse_poly(row["A_poly"]), parse_poly(row["B_poly"])
    l, m, d_base = row["ell"], row["m"], row["d_exact"]
    out = {"instance_id": row["instance_id"], "code_id": row["code_id"],
           "group": row["group_struct"], "ell": l, "m": m,
           "n": row["n"], "k": row["k"], "d_base": d_base,
           "A": row["A_poly"], "B": row["B_poly"], "axis": axis,
           "floor": 2 * d_base}

    # k-gate (condition 2): k preserved <=> (R) holds (A12)
    Ac, Bc, lc, mc = canonical_row(A, B, l, m, axis)
    cov = XCover(Ac, Bc, lc, mc)
    kb = h1_dim(cov.d2b, cov.d1b)
    kc = h1_dim(cov.d2c, cov.d1c)
    out["k_base_recomputed"], out["k_cover"] = kb, kc
    if kb != row["k"]:
        out["warn"] = f"k mismatch: corpus {row['k']}, recomputed {kb}"
    if kc != kb:
        out["status"] = "K-GATE-FAIL"
        out["secs"] = round(time.time() - t0, 1)
        return out

    # cheap tiers S0/S1+/S2 (per-class detail persisted for Phase 3)
    rec = screen_row_phase2(A, B, l, m, axis, d_base)
    out.update({"dim_ker_d2": rec["dim_ker_d2"], "per_class": rec["per_class"],
                "best": rec["best"], "cheap_min": rec["min_reached"]})
    if rec["reject"]:
        out["status"] = "CHEAP-REJECT"
        out["deficit"] = out["floor"] - rec["min_reached"]
        out["secs"] = round(time.time() - t0, 1)
        return out

    if not run_s4:
        out["status"] = "CHEAP-PASS"
        out["secs"] = round(time.time() - t0, 1)
        return out

    # S4: orbit-rep coset SAT at floor-1
    s4 = s4_run(A, B, l, m, axis, d_base, conf_budget)
    out["s4"] = s4
    out["status"] = s4["status"]
    if s4["status"] == "SF-REFUTED":
        wts = [v["weight"] for v in s4["verdicts"] if v.get("weight")]
        out["deficit"] = out["floor"] - min(wts)
    if s4["status"] == "SF-CERTIFIED" and run_ladder:
        out["cover"] = cover_distance_ladder(row["A_poly"], row["B_poly"],
                                             l, m, axis, 2 * d_base)
    out["secs"] = round(time.time() - t0, 1)
    return out


# ------------------------------------------------------------ validation


def validate(conf_budget: int) -> bool:
    """Gate: reproduce SS14 (d10_battery.json) + SF-true anchors cheap-pass."""
    ok = True

    print("== validation 1/3: x^21-1 factor table (asserted at import) ==")
    blocks = p2.block_idempotent_supports(21, 3)
    dims = sum(len(b) for b in blocks)  # supports partition mass, not dim
    print(f"  Z21xZ3 idempotent blocks: {len(blocks)} (support mass {dims})")

    print("== validation 2/3: reproduce SS14 d=10 battery verdicts ==")
    expected = {
        ("x^9 + y + y^2", "1 + x^2 + x^7", 15, 3, "x"):
            ("CHEAP-REJECT", 10),
        ("x^9 + y + y^2", "1 + x^2 + x^7", 15, 3, "y"):
            ("CHEAP-REJECT", 10),
        ("x^3 + y + y^2", "y^3 + x + x^2", 9, 6, "x"):
            ("K-GATE-FAIL", None),
        ("x^3 + y + y^2", "y^3 + x + x^2", 9, 6, "y"):
            ("CHEAP-REJECT", 18),
    }
    for (As, Bs, l, m, axis), (want, want_min) in expected.items():
        row = {"instance_id": f"val-{axis}", "code_id": "val",
               "group_struct": f"Z{l}xZ{m}", "ell": l, "m": m,
               "n": 2 * l * m, "k": 8, "d_exact": 10,
               "A_poly": As, "B_poly": Bs}
        r = process_cell(row, axis, conf_budget, run_s4=False,
                         run_ladder=False)
        got_min = r.get("cheap_min")
        good = r["status"] == want and (want_min is None
                                        or got_min == want_min)
        ok &= good
        print(f"  [{l}x{m}:{axis}] want {want}/{want_min} "
              f"got {r['status']}/{got_min} "
              f"{'OK' if good else 'MISMATCH'}")

    print("== validation 3/3: SF-true anchors must not be rejected ==")
    anchors = [
        ("pair72-base [[36,4,4]] x", "x^2 + y + y^3", "1 + x + y^2",
         3, 6, "x", 4),
        ("gross-base [[72,12,6]] x", "x^3 + y + y^2", "y^3 + x + x^2",
         6, 6, "x", 6),
    ]
    for name, As, Bs, l, m, axis, d in anchors:
        row = {"instance_id": f"anchor-{name.split()[0]}", "code_id": "anchor",
               "group_struct": f"Z{l}xZ{m}", "ell": l, "m": m,
               "n": 2 * l * m, "k": None, "d_exact": d,
               "A_poly": As, "B_poly": Bs}
        r = process_cell(row, axis, conf_budget, run_s4=True,
                         run_ladder=False)
        good = r["status"] in ("CHEAP-PASS", "SF-CERTIFIED")
        ok &= good
        print(f"  {name}: {r['status']} "
              f"{'OK' if good else 'FALSE REJECTION — bug'}")

    print(f"\nVALIDATION {'GREEN' if ok else 'FAILED'}")
    return ok


# ------------------------------------------------------------ drivers


def load_done(out_dir: Path) -> set[tuple]:
    """Cells recorded in ANY corpus_battery*.jsonl (all shards/sessions)."""
    done = set()
    for path in sorted(out_dir.glob("corpus_battery*.jsonl")):
        for line in open(path):
            r = json.loads(line)
            done.add((r["instance_id"], r["axis"]))
    return done


def run(strata: list[int], out_path: Path, conf_budget: int, limit: int,
        run_s4: bool, run_ladder: bool, group: str | None,
        shard: str | None) -> None:
    corpus = Corpus().filter(d_exact_in=strata, k_gte=1)
    if group:
        corpus = corpus.filter(group_struct=group)
    rows = sorted(corpus, key=lambda r: (-r["d_exact"], r["n"],
                                         r["instance_id"]))
    cells = [(r, ax) for r in rows for ax in ("x", "y")]
    if shard:
        # Split BEFORE the done-filter: `cells` is deterministic (static DB,
        # fixed sort), so worker splits stay disjoint + complete even though
        # workers start at different times with different done-sets.
        k, n = (int(t) for t in shard.split("/"))
        cells = cells[k::n]
    done = load_done(out_path.parent)
    todo = [(r, ax) for r, ax in cells
            if (r["instance_id"], ax) not in done]
    if limit:
        todo = todo[:limit]
    print(f"strata {strata}: {len(rows)} rows -> {len(cells)} cells, "
          f"{len(done)} done, {len(todo)} to run", flush=True)

    counts: dict[str, int] = {}
    t0 = time.time()
    with open(out_path, "a") as fh:
        for i, (r, ax) in enumerate(todo):
            rec = process_cell(r, ax, conf_budget, run_s4, run_ladder)
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            counts[rec["status"]] = counts.get(rec["status"], 0) + 1
            hot = rec["status"] in ("CHEAP-PASS", "SF-CERTIFIED",
                                    "INCONCLUSIVE")
            if hot or (i + 1) % 25 == 0:
                el = time.time() - t0
                line = (f"  [{i + 1}/{len(todo)} {el:.0f}s] "
                        f"{r['instance_id']}:{ax} d={r['d_exact']} "
                        f"-> {rec['status']}")
                if "cheap_min" in rec:
                    line += (f" (min {rec['cheap_min']}/"
                             f"floor {rec['floor']})")
                if hot:
                    line = "*** " + line
                print(line, flush=True)
    print(f"\ndone in {time.time() - t0:.0f}s: {counts}", flush=True)


def summarize(out_path: Path) -> None:
    """Summarize ALL corpus_battery*.jsonl shards, deduped by cell."""
    seen: dict[tuple, dict] = {}
    for path in sorted(out_path.parent.glob("corpus_battery*.jsonl")):
        for line in open(path):
            r = json.loads(line)
            seen.setdefault((r["instance_id"], r["axis"]), r)
    rows = list(seen.values())
    from collections import Counter
    print(f"{len(rows)} distinct cells across "
          f"{out_path.parent}/corpus_battery*.jsonl")
    by_stratum: dict[int, Counter] = {}
    for r in rows:
        by_stratum.setdefault(r["d_base"], Counter())[r["status"]] += 1
    for d in sorted(by_stratum, reverse=True):
        print(f"  d={d} (floor {2 * d}): {dict(by_stratum[d])}")
    print("\ndeficit histogram (floor - reached), rejects only:")
    defs = Counter(r["deficit"] for r in rows if "deficit" in r)
    for k in sorted(defs):
        print(f"  deficit {k:3d}: {defs[k]}")
    hot = [r for r in rows if r["status"] in
           ("CHEAP-PASS", "SF-CERTIFIED", "INCONCLUSIVE")]
    near = [r for r in rows if r.get("deficit") is not None
            and r["deficit"] <= 2]
    print(f"\nhot cells (pass/certified/inconclusive): {len(hot)}")
    for r in hot:
        print(f"  {r['instance_id']}:{r['axis']} [{r['group']}] "
              f"d={r['d_base']} -> {r['status']}"
              + (f" cover={r['cover']}" if "cover" in r else ""))
    print(f"near-misses (deficit <= 2): {len(near)}")
    for r in near:
        print(f"  {r['instance_id']}:{r['axis']} [{r['group']}] "
              f"d={r['d_base']} deficit={r['deficit']} ({r['status']})")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--strata", default="12,10,8",
                    help="comma-separated d_exact values (default 12,10,8)")
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    ap.add_argument("--conf-budget", type=int, default=10_000_000)
    ap.add_argument("--limit", type=int, default=0,
                    help="cap number of cells this run (0 = no cap)")
    ap.add_argument("--group", default=None,
                    help="restrict to one group_struct")
    ap.add_argument("--shard", default=None,
                    help="K/N: run cells K::N of the todo list "
                         "(all workers must start with the same done-set)")
    ap.add_argument("--no-s4", action="store_true",
                    help="cheap tiers only (record CHEAP-PASS)")
    ap.add_argument("--no-ladder", action="store_true",
                    help="skip the cover distance ladder on SF-CERTIFIED")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--summarize", action="store_true")
    args = ap.parse_args()

    if args.validate:
        sys.exit(0 if validate(args.conf_budget) else 1)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    if args.summarize:
        summarize(out_path)
        return
    strata = [int(s) for s in args.strata.split(",")]
    run(strata, out_path, args.conf_budget, args.limit,
        run_s4=not args.no_s4, run_ladder=not args.no_ladder,
        group=args.group, shard=args.shard)


if __name__ == "__main__":
    main()

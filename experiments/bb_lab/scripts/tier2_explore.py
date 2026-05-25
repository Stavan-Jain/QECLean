"""Tier-2 first-conjecture-mill exploration.

Take the corpus of BB instances with `d_exact` filled in, evaluate
candidate distance bounds, and emit a tightness report.

Usage (from `experiments/bb_lab/`):

    uv run python scripts/tier2_explore.py
    uv run python scripts/tier2_explore.py --db /path/to/other.duckdb
    uv run python scripts/tier2_explore.py --groups Z3xZ4 Z3xZ5

The script is **read-only**. It uses `Corpus(...)` and will fail with
a clear error if a `bb-lab enumerate` / `fill-distances` writer is
holding the DB lock (DuckDB blocks even read-only access in that case).

Output: one block per candidate bound:
  - bound name + formula
  - rows applicable (have d_exact and the predictors needed)
  - tight count (looseness = 0)
  - mean / median looseness
  - per-group breakdown
  - example tight + example loose row id

This is the *substrate* for conjecture work — the script doesn't claim
any candidate bound is novel. Each candidate carries a citation note;
the textbook bound `d_X ≤ min(d_A^⊥, d_B^⊥)` was already established
in the b5de5dd commit (see CSS distance theory; specifically
Calderbank-Shor / Steane / Lin-Pryadko 2306.16400 §IV-V).

Stub-bound candidates supported:

  CSS_classical_lb  →  d_X ≤ min(min_wt_ker_A, min_wt_ker_B)
  weight_per_check  →  d_X ≤ A_weight + B_weight (loose, included as a
                       sanity check that the corpus / orientation work)

Add more by extending `CANDIDATES`.
"""

from __future__ import annotations

import argparse
import statistics
from dataclasses import dataclass
from pathlib import Path

from bb_lab.corpus import Corpus


@dataclass(frozen=True, slots=True)
class Candidate:
    name: str
    formula: str
    citation: str
    # Required column names that must be non-null on the row.
    requires: tuple[str, ...]
    # bound(row) -> int upper bound. row is a dict (Corpus iter dict).
    bound_fn: object  # callable[[dict], int]


CANDIDATES: tuple[Candidate, ...] = (
    Candidate(
        name="CSS_classical_dual",
        formula="d_X ≤ min(min_wt_ker_A, min_wt_ker_B)",
        citation=(
            "Standard CSS dual upper bound (textbook; see Calderbank-Shor, "
            "Steane, or Lin-Pryadko 2306.16400 §IV–V). Encoded earlier in "
            "commit b5de5dd."
        ),
        requires=("min_wt_ker_A", "min_wt_ker_B"),
        bound_fn=lambda r: min(r["min_wt_ker_A"], r["min_wt_ker_B"]),
    ),
    Candidate(
        name="check_weight_sum",
        formula="d_X ≤ A_weight + B_weight",
        citation=(
            "Trivial upper bound: any single H_X row IS an X-stabilizer (so "
            "it's IN rowspan(H_X)), but it bounds the stab subgroup's "
            "minimum weight, NOT the logical minimum weight — included as "
            "a sanity check that orientation is consistent post-migration."
        ),
        requires=("A_weight", "B_weight"),
        bound_fn=lambda r: r["A_weight"] + r["B_weight"],
    ),
    Candidate(
        name="tanner_girth_upper",
        formula="d_X ≤ floor((n_qubits + tanner_girth) / 2) (very loose)",
        citation=(
            "Tanner-graph diameter-style bound, well-known for qLDPC codes; "
            "very loose for engineered BB codes. Mostly here to demonstrate "
            "how to surface multi-feature candidates."
        ),
        requires=("n", "tanner_girth"),
        bound_fn=lambda r: (
            r["n"] + max(r["tanner_girth"], 0)
        ) // 2,
    ),
)


def evaluate_candidate(
    corpus: Corpus, cand: Candidate, group_filter: list[str] | None,
) -> dict:
    """Run `cand` over every row with a `d_exact` and the required
    predictor columns. Return a structured report.

    Missing columns (e.g. `min_wt_ker_A` on a corpus that hasn't run
    `fill-features` yet) are detected up-front; the candidate is
    reported as 0-applicable rather than blowing up on the SQL query.
    """
    available_cols = set(corpus.columns())
    missing = [c for c in cand.requires if c not in available_cols]
    if missing:
        return {
            "name": cand.name,
            "formula": cand.formula,
            "citation": cand.citation,
            "applicable_rows": 0,
            "note": (
                f"corpus is missing required column(s) {missing}; "
                f"run `bb-lab fill-features` to populate them"
            ),
        }

    base = corpus.filter(d_exact_is_not_null=True)
    if group_filter:
        base = base.filter(group_struct_in=list(group_filter))
    for col in cand.requires:
        base = base.filter(**{f"{col}_is_not_null": True})
    rows = list(base)
    if not rows:
        return {
            "name": cand.name,
            "formula": cand.formula,
            "citation": cand.citation,
            "applicable_rows": 0,
            "note": "no rows with all required fields filled in",
        }

    looseness: list[int] = []
    tight_examples: list[dict] = []
    loose_examples: list[dict] = []
    violations: list[dict] = []
    per_group_tight: dict[str, list[int]] = {}
    per_group_total: dict[str, int] = {}

    for r in rows:
        try:
            bound = int(cand.bound_fn(r))
        except Exception as e:
            violations.append({"row": r["instance_id"], "error": str(e)})
            continue
        d = int(r["d_exact"])
        diff = bound - d
        looseness.append(diff)
        g = r["group_struct"]
        per_group_total[g] = per_group_total.get(g, 0) + 1
        if diff < 0:
            # The bound is supposed to be an UPPER bound on d. A
            # violation means the candidate has a bug or is just wrong.
            violations.append({
                "row": r["instance_id"], "d_exact": d,
                "bound": bound, "diff": diff,
            })
        if diff == 0:
            per_group_tight.setdefault(g, []).append(1)
            if len(tight_examples) < 3:
                tight_examples.append({
                    "id": r["instance_id"], "group": g,
                    "n": r["n"], "k": r["k"], "d": d,
                    "bound": bound,
                })
        else:
            if len(loose_examples) < 3:
                loose_examples.append({
                    "id": r["instance_id"], "group": g,
                    "n": r["n"], "k": r["k"], "d": d,
                    "bound": bound, "diff": diff,
                })

    return {
        "name": cand.name,
        "formula": cand.formula,
        "citation": cand.citation,
        "applicable_rows": len(rows),
        "tight_count": sum(1 for x in looseness if x == 0),
        "tight_rate": sum(1 for x in looseness if x == 0) / max(len(looseness), 1),
        "mean_looseness": statistics.mean(looseness) if looseness else None,
        "median_looseness": statistics.median(looseness) if looseness else None,
        "max_looseness": max(looseness) if looseness else None,
        "min_looseness": min(looseness) if looseness else None,
        "violations": violations,
        "per_group_tight": {
            g: (len(per_group_tight.get(g, [])), per_group_total[g])
            for g in per_group_total
        },
        "tight_examples": tight_examples,
        "loose_examples": loose_examples,
    }


def render_report(reports: list[dict]) -> str:
    out: list[str] = []
    for r in reports:
        out.append(f"\n=== {r['name']} ===")
        out.append(f"  formula: {r['formula']}")
        out.append(f"  citation: {r['citation']}")
        if "note" in r:
            out.append(f"  note: {r['note']}")
            continue
        out.append(f"  applicable rows: {r['applicable_rows']}")
        out.append(
            f"  tight (looseness=0): {r['tight_count']} "
            f"({r['tight_rate']*100:.1f}% of applicable)"
        )
        out.append(
            f"  looseness  min={r['min_looseness']}  median={r['median_looseness']}  "
            f"mean={r['mean_looseness']:.2f}  max={r['max_looseness']}"
            if r["mean_looseness"] is not None else "  looseness: n/a"
        )
        if r["violations"]:
            out.append(f"  VIOLATIONS ({len(r['violations'])}):")
            for v in r["violations"][:5]:
                out.append(f"    {v}")
        out.append("  per group (tight / total):")
        for g in sorted(r["per_group_tight"]):
            tight, total = r["per_group_tight"][g]
            out.append(
                f"    {g:10s}  {tight:4d} / {total:4d}  ({tight/max(total,1)*100:.1f}%)"
            )
        if r["tight_examples"]:
            out.append("  tight examples:")
            for e in r["tight_examples"]:
                out.append(
                    f"    {e['id'][:8]}  {e['group']:10s}  "
                    f"n={e['n']}  k={e['k']}  d={e['d']}  bound={e['bound']}"
                )
        if r["loose_examples"]:
            out.append("  loose examples:")
            for e in r["loose_examples"]:
                out.append(
                    f"    {e['id'][:8]}  {e['group']:10s}  "
                    f"n={e['n']}  k={e['k']}  d={e['d']}  bound={e['bound']}  "
                    f"(loose by {e['diff']})"
                )
    return "\n".join(out)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    ap.add_argument(
        "--db", type=Path, default=None,
        help="Path to a bb_instances.duckdb (default: lab's data/bb_instances.duckdb)",
    )
    ap.add_argument(
        "--groups", nargs="*", default=None,
        help="Restrict to these group_struct labels (default: all groups in DB)",
    )
    args = ap.parse_args()

    corpus = Corpus(db_path=args.db) if args.db else Corpus()
    summary = corpus.summary()
    print(f"corpus: {summary}")
    reports = [
        evaluate_candidate(corpus, c, args.groups) for c in CANDIDATES
    ]
    print(render_report(reports))


if __name__ == "__main__":
    main()

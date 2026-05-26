"""Tier-3 corpus sweep: test the Jacobson-radical conjecture.

For every row in the corpus with `d_exact` filled, compute the bound

    bound  =  Σ_{O ∈ V_A ∩ V_B}  |O| · min(μ_O(A), μ_O(B))

and compare to `d_exact`. **Violation** = bound > d_exact. A single
violation falsifies the conjecture.

Outputs to stdout. Pipe to a notes file for the corpus-sweep write-up.
"""

from __future__ import annotations

import argparse
import time
from collections import defaultdict
from pathlib import Path

from bb_lab.algebraic_features import jacobson_radical_bound
from bb_lab.corpus import Corpus
from bb_lab.group import ZmZn
from bb_lab.poly import Poly


def sweep(corpus: Corpus, max_rows: int | None = None):
    rows = corpus.filter(d_exact_is_not_null=True)
    if max_rows is not None:
        rows = rows.limited(max_rows)

    per_group: dict[str, dict] = defaultdict(
        lambda: dict(n=0, tight=0, loose=0, violations=0, gap_sum=0, gap_max=0)
    )
    overall: dict = dict(n=0, tight=0, loose=0, violations=0, gap_sum=0, gap_max=0)
    violations: list[dict] = []
    near_tight: list[dict] = []
    gap_dist: defaultdict[int, int] = defaultdict(int)

    t0 = time.time()
    n_total = 0
    for r in rows:
        ell = int(r["ell"])
        m = int(r["m"])
        G = ZmZn(ell, m)
        A = Poly.from_string(r["A_poly"], G)
        B = Poly.from_string(r["B_poly"], G)
        d = int(r["d_exact"])
        bound = jacobson_radical_bound(A, B, G)
        gap = d - bound  # > 0 → bound holds; < 0 → violation
        n_total += 1

        gs = r["group_struct"]
        per_group[gs]["n"] += 1
        overall["n"] += 1
        if gap < 0:
            per_group[gs]["violations"] += 1
            overall["violations"] += 1
            violations.append(dict(
                code_id=r["code_id"], group=gs, A=r["A_poly"], B=r["B_poly"],
                d_exact=d, bound=bound, gap=gap, n=int(r["n"]), k=int(r["k"]),
            ))
        elif gap == 0:
            per_group[gs]["tight"] += 1
            overall["tight"] += 1
            if d > 0:  # only count nontrivial tight cases
                near_tight.append(dict(
                    code_id=r["code_id"], group=gs, A=r["A_poly"], B=r["B_poly"],
                    d_exact=d, bound=bound, n=int(r["n"]), k=int(r["k"]),
                ))
        else:
            per_group[gs]["loose"] += 1
            overall["loose"] += 1
        per_group[gs]["gap_sum"] += gap
        overall["gap_sum"] += gap
        per_group[gs]["gap_max"] = max(per_group[gs]["gap_max"], gap)
        overall["gap_max"] = max(overall["gap_max"], gap)
        gap_dist[gap] += 1

        if n_total % 200 == 0:
            elapsed = time.time() - t0
            print(f"  ...{n_total} rows ({elapsed:.1f}s, "
                  f"{n_total/elapsed:.0f} rows/s); violations={overall['violations']}, "
                  f"tight={overall['tight']}", flush=True)

    return per_group, overall, violations, near_tight, gap_dist


def render(per_group, overall, violations, near_tight, gap_dist):
    out: list[str] = []
    out.append("# T3.2 — Tier-3 Corpus sweep: Jacobson-radical conjecture")
    out.append("")
    out.append(
        "Tests `d_exact ≥ Σ_{O ∈ V_A ∩ V_B} |O| · min(μ_O(A), μ_O(B))` "
        "across all corpus rows with `d_exact` populated."
    )
    out.append("")
    out.append("## Overall")
    out.append("")
    n = overall["n"]
    if n == 0:
        out.append("No rows in sweep.")
        return "\n".join(out)
    out.append(f"- Total rows with d_exact: **{n}**")
    out.append(f"- Violations (bound > d_exact): **{overall['violations']}**")
    out.append(f"- Tight (bound = d_exact, d > 0): {overall['tight']}")
    out.append(f"- Loose (bound < d_exact): {overall['loose']}")
    out.append(f"- Tightness rate (tight / total): {overall['tight']/n:.1%}")
    out.append(
        f"- Average gap (d - bound): {overall['gap_sum']/n:.2f}, max: {overall['gap_max']}"
    )
    out.append("")
    if overall["violations"] == 0:
        out.append("**No violations — conjecture survives this corpus sweep.**")
    else:
        out.append("**Violations found — conjecture is FALSIFIED.**")
    out.append("")

    out.append("## Per-group breakdown")
    out.append("")
    out.append("| Group | rows | violations | tight | loose | tightness | avg gap | max gap |")
    out.append("|---|---:|---:|---:|---:|---:|---:|---:|")
    for gs, st in sorted(per_group.items()):
        rate = st["tight"] / st["n"] if st["n"] else 0
        avg = st["gap_sum"] / st["n"] if st["n"] else 0
        out.append(
            f"| {gs} | {st['n']} | {st['violations']} | {st['tight']} | {st['loose']} | "
            f"{rate:.1%} | {avg:.2f} | {st['gap_max']} |"
        )
    out.append("")

    out.append("## Gap distribution")
    out.append("")
    out.append("Gap = d_exact - bound. Negative = violation; 0 = tight; positive = loose.")
    out.append("")
    out.append("| Gap | Count |")
    out.append("|---:|---:|")
    for gap in sorted(gap_dist.keys()):
        out.append(f"| {gap} | {gap_dist[gap]} |")
    out.append("")

    if violations:
        out.append("## Violations (FALSIFICATION CASES)")
        out.append("")
        out.append("| code_id | group | A | B | d | bound | gap | n | k |")
        out.append("|---|---|---|---|---:|---:|---:|---:|---:|")
        for v in sorted(violations, key=lambda x: x["gap"])[:50]:
            out.append(
                f"| {v['code_id']} | {v['group']} | {v['A']} | {v['B']} | "
                f"{v['d_exact']} | {v['bound']} | {v['gap']} | {v['n']} | {v['k']} |"
            )
        if len(violations) > 50:
            out.append(f"... ({len(violations) - 50} more)")
        out.append("")

    if near_tight:
        out.append("## Tight cases (sample)")
        out.append("")
        out.append("| code_id | group | A | B | d | bound | n | k |")
        out.append("|---|---|---|---|---:|---:|---:|---:|")
        for nt in sorted(near_tight, key=lambda x: -x["d_exact"])[:20]:
            out.append(
                f"| {nt['code_id']} | {nt['group']} | {nt['A']} | {nt['B']} | "
                f"{nt['d_exact']} | {nt['bound']} | {nt['n']} | {nt['k']} |"
            )
        out.append("")

    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-rows", type=int, default=None)
    ap.add_argument("--output", type=Path, default=None,
                    help="If set, write report to this file. Default: stdout.")
    args = ap.parse_args()

    corpus = Corpus()
    print(f"Corpus: {corpus.summary()}", flush=True)
    per_group, overall, violations, near_tight, gap_dist = sweep(corpus, args.max_rows)
    report = render(per_group, overall, violations, near_tight, gap_dist)
    if args.output:
        args.output.write_text(report)
        print(f"Wrote report to {args.output}")
    else:
        print(report)


if __name__ == "__main__":
    main()

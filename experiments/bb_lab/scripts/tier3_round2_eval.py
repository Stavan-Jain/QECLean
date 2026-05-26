"""Tier-3 round 2: evaluate the *real* Jacobson-radical bound on the
non-degenerate subset of the BB corpus.

Round 1's conjecture was

    d_X(BB(G, A, B))  ≥  Σ_{O ∈ V_A ∩ V_B}  |O| · min(μ_O(A), μ_O(B))

and was falsified universally on 10.5% of the corpus. A quick query
revealed that violations concentrate on **degenerate** codes (those
where `⟨supp(A)⟩ < G` or `⟨supp(B)⟩ < G`). Round 2 stress-tests the
**conditional** version restricted to non-degenerate codes.

This script:
  1. Reads every corpus row with `d_exact` populated.
  2. Classifies each row as non-degenerate via
     `bb_lab.degeneracy.is_non_degenerate(A, B, G)`.
  3. Computes `jacobson_radical_bound(A, B, G)` (the *real* RHS, not
     the proxy `k/2`).
  4. Records `(row_id, group_struct, n, k, d_exact, bound, slack, is_violation)`.
  5. Writes raw data to `data/t3r2_nondegenerate_eval.parquet`.
  6. Writes a human-readable summary to `notes/T3R2.2_nondegenerate_eval.md`.

Run from `experiments/bb_lab/`:

    uv run python scripts/tier3_round2_eval.py
"""

from __future__ import annotations

import argparse
import time
from collections import defaultdict
from pathlib import Path

import pyarrow as pa
import pyarrow.parquet as pq

from bb_lab.algebraic_features import jacobson_radical_bound
from bb_lab.corpus import Corpus
from bb_lab.degeneracy import is_non_degenerate, supp_generates_G
from bb_lab.group import ZmZn
from bb_lab.poly import Poly


LAB_ROOT = Path(__file__).resolve().parent.parent
DATA_PATH = LAB_ROOT / "data" / "t3r2_nondegenerate_eval.parquet"
NOTES_PATH = LAB_ROOT / "notes" / "T3R2.2_nondegenerate_eval.md"


def evaluate(corpus: Corpus, max_rows: int | None = None) -> list[dict]:
    """Walk the corpus once; return one record per row with `d_exact`."""
    rows = corpus.filter(d_exact_is_not_null=True)
    if max_rows is not None:
        rows = rows.limited(max_rows)

    out: list[dict] = []
    t0 = time.time()
    n_processed = 0
    for r in rows:
        ell, m = int(r["ell"]), int(r["m"])
        G = ZmZn(ell, m)
        A = Poly.from_string(r["A_poly"], G)
        B = Poly.from_string(r["B_poly"], G)
        d = int(r["d_exact"])

        a_nd = supp_generates_G(A, G)
        b_nd = supp_generates_G(B, G)
        nondeg = a_nd and b_nd

        # Compute the bound unconditionally — interesting for the full
        # corpus shape too, and not expensive at corpus scale.
        bound = jacobson_radical_bound(A, B, G)
        slack = d - bound  # > 0: loose; 0: tight; < 0: violation
        violation = slack < 0

        out.append(dict(
            instance_id=str(r["instance_id"]),
            code_id=str(r["code_id"]),
            group_struct=str(r["group_struct"]),
            ell=ell, m=m,
            n=int(r["n"]),
            k=int(r["k"]),
            A_poly=str(r["A_poly"]),
            B_poly=str(r["B_poly"]),
            A_weight=int(r["A_weight"]),
            B_weight=int(r["B_weight"]),
            A_nondeg=bool(a_nd),
            B_nondeg=bool(b_nd),
            nondegenerate=bool(nondeg),
            d_exact=d,
            jacobson_bound=int(bound),
            slack=int(slack),
            violation=bool(violation),
            half_k=int(r["k"]) // 2,  # the *proxy* RHS for round-1 sanity
        ))

        n_processed += 1
        if n_processed % 500 == 0:
            elapsed = time.time() - t0
            print(
                f"  ...{n_processed} rows ({elapsed:.1f}s, "
                f"{n_processed/elapsed:.0f} rows/s)",
                flush=True,
            )
    elapsed = time.time() - t0
    print(f"Total: {n_processed} rows in {elapsed:.1f}s")
    return out


def write_parquet(records: list[dict], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    table = pa.Table.from_pylist(records)
    pq.write_table(table, str(path))


def aggregate(records: list[dict]) -> dict:
    """Compute the summary numbers used in the verdict write-up."""
    total = len(records)
    nondeg_records = [r for r in records if r["nondegenerate"]]
    deg_records = [r for r in records if not r["nondegenerate"]]

    n_nondeg = len(nondeg_records)
    n_deg = len(deg_records)

    # Violations of the *real* Jacobson bound on each partition.
    nondeg_violations = [r for r in nondeg_records if r["violation"]]
    deg_violations = [r for r in deg_records if r["violation"]]

    # Per-group breakdowns over the non-degenerate subset.
    nondeg_per_group: dict[str, dict[str, int]] = defaultdict(
        lambda: dict(n=0, violations=0, tight=0, loose=0)
    )
    nondeg_violation_per_group: dict[str, int] = defaultdict(int)
    deg_violation_per_group: dict[str, int] = defaultdict(int)

    for r in nondeg_records:
        gs = r["group_struct"]
        nondeg_per_group[gs]["n"] += 1
        if r["slack"] < 0:
            nondeg_per_group[gs]["violations"] += 1
            nondeg_violation_per_group[gs] += 1
        elif r["slack"] == 0:
            nondeg_per_group[gs]["tight"] += 1
        else:
            nondeg_per_group[gs]["loose"] += 1
    for r in deg_records:
        if r["slack"] < 0:
            deg_violation_per_group[r["group_struct"]] += 1

    # Slack distribution on non-degenerate subset.
    slack_dist: dict[int, int] = defaultdict(int)
    for r in nondeg_records:
        slack_dist[r["slack"]] += 1

    # Proxy-vs-real comparison on the non-degenerate subset.
    proxy_violations = [
        r for r in nondeg_records if r["d_exact"] < r["half_k"]
    ]

    return dict(
        total=total,
        n_nondeg=n_nondeg,
        n_deg=n_deg,
        nondeg_violations=nondeg_violations,
        deg_violations=deg_violations,
        n_nondeg_violations=len(nondeg_violations),
        n_deg_violations=len(deg_violations),
        nondeg_per_group=dict(nondeg_per_group),
        nondeg_violation_per_group=dict(nondeg_violation_per_group),
        deg_violation_per_group=dict(deg_violation_per_group),
        slack_dist=dict(slack_dist),
        proxy_violations=proxy_violations,
        n_proxy_violations=len(proxy_violations),
    )


def render(summary: dict) -> str:
    out: list[str] = []
    out.append("# T3R2.2 — Real Jacobson bound on non-degenerate BB corpus")
    out.append("")
    out.append(
        "Tier-3 round 2 evaluates the **conditional** Jacobson-radical conjecture"
    )
    out.append("")
    out.append("> For non-degenerate BB codes,")
    out.append("> `d_X(BB(G, A, B)) ≥ Σ_{O ∈ V_A ∩ V_B} |O| · min(μ_O(A), μ_O(B))`")
    out.append(">")
    out.append("> where non-degenerate means `⟨supp(A)⟩ = G = ⟨supp(B)⟩`.")
    out.append("")
    out.append("**Source data**: every corpus row with `d_exact` filled in.")
    out.append("")

    out.append("## Headline numbers")
    out.append("")
    out.append(f"- Total rows with `d_exact`: **{summary['total']}**")
    out.append(
        f"- Non-degenerate rows: **{summary['n_nondeg']}** "
        f"({summary['n_nondeg']/summary['total']:.1%})"
    )
    out.append(
        f"- Degenerate rows: **{summary['n_deg']}** "
        f"({summary['n_deg']/summary['total']:.1%})"
    )
    out.append("")

    out.append("### Violations of the *real* Jacobson bound")
    out.append("")
    n_nd = summary["n_nondeg"]
    n_v = summary["n_nondeg_violations"]
    out.append(
        f"- Non-degenerate violations (d_exact < jacobson_bound): "
        f"**{n_v}** / **{n_nd}** "
        f"({(n_v / n_nd if n_nd else 0):.1%})"
    )
    n_d = summary["n_deg"]
    n_dv = summary["n_deg_violations"]
    out.append(
        f"- Degenerate violations: {n_dv} / {n_d} "
        f"({(n_dv / n_d if n_d else 0):.1%})"
    )
    out.append("")

    out.append("### Proxy vs. real on the non-degenerate subset")
    out.append("")
    out.append(
        f"- Proxy `d ≥ k/2` violations: {summary['n_proxy_violations']} "
        f"({summary['n_proxy_violations']/n_nd:.1%})"
    )
    out.append(
        f"- Real bound `d ≥ Σ|O|·μ_O` violations: {n_v} ({n_v/n_nd:.1%})"
    )
    out.append("")
    out.append(
        "The real bound is generally ≥ the proxy `k/2` since the latter is the"
    )
    out.append(
        "semisimple-quotient kernel count; the real bound adds Jacobson-radical depth."
    )
    out.append("")

    out.append("## Per-group breakdown (non-degenerate only)")
    out.append("")
    out.append("| group | rows | violations | tight | loose | violation rate |")
    out.append("|---|---:|---:|---:|---:|---:|")
    for gs in sorted(summary["nondeg_per_group"].keys()):
        st = summary["nondeg_per_group"][gs]
        rate = st["violations"] / st["n"] if st["n"] else 0
        out.append(
            f"| {gs} | {st['n']} | {st['violations']} | {st['tight']} | "
            f"{st['loose']} | {rate:.1%} |"
        )
    out.append("")

    out.append("## Slack distribution (non-degenerate only)")
    out.append("")
    out.append("Slack = d_exact - jacobson_bound. Negative = violation.")
    out.append("")
    out.append("| slack | count |")
    out.append("|---:|---:|")
    for slack in sorted(summary["slack_dist"].keys()):
        out.append(f"| {slack} | {summary['slack_dist'][slack]} |")
    out.append("")

    if summary["nondeg_violations"]:
        out.append("## Sample non-degenerate violators (first 20 by slack)")
        out.append("")
        out.append("| code_id | group | A | B | n | k | d | bound | slack |")
        out.append("|---|---|---|---|---:|---:|---:|---:|---:|")
        for v in sorted(
            summary["nondeg_violations"], key=lambda r: (r["slack"], r["n"])
        )[:20]:
            out.append(
                f"| {v['code_id']} | {v['group_struct']} | "
                f"{v['A_poly']} | {v['B_poly']} | "
                f"{v['n']} | {v['k']} | {v['d_exact']} | "
                f"{v['jacobson_bound']} | {v['slack']} |"
            )
        out.append("")
    return "\n".join(out)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-rows", type=int, default=None)
    ap.add_argument(
        "--data-path", type=Path, default=DATA_PATH,
        help=f"Where to write raw parquet (default {DATA_PATH})",
    )
    ap.add_argument(
        "--notes-path", type=Path, default=NOTES_PATH,
        help=f"Where to write summary md (default {NOTES_PATH})",
    )
    args = ap.parse_args()

    corpus = Corpus()
    print(f"Corpus: {corpus.summary()}", flush=True)

    records = evaluate(corpus, args.max_rows)
    write_parquet(records, args.data_path)
    print(f"Wrote raw evaluation to {args.data_path}")

    summary = aggregate(records)
    notes = render(summary)
    args.notes_path.parent.mkdir(parents=True, exist_ok=True)
    args.notes_path.write_text(notes)
    print(f"Wrote summary to {args.notes_path}")

    print()
    print("=== headline ===")
    print(f"  total rows with d_exact: {summary['total']}")
    print(f"  non-degenerate: {summary['n_nondeg']}")
    print(f"  non-degenerate violations: {summary['n_nondeg_violations']}")
    print(f"  proxy d<k/2 violations on nondeg: {summary['n_proxy_violations']}")


if __name__ == "__main__":
    main()

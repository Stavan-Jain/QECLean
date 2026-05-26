"""Tier-2 Round 2 candidate evaluation against corpus + Bravyi table.

For each candidate in `tier2_candidates_r2.R2_CANDIDATES`:
1. Compute the bound on every corpus row.
2. Report tightness, violations, mean/max looseness.
3. Compute on each Bravyi-table reference instance
   (`bb_72_12_6`, `bb_90_8_10`, `bb_108_8_10`, `gross`,
   `bb_288_12_18`) and report whether the bound matches d.

Output: `notes/T2R2.4_evaluation.md` with per-candidate breakdown.

Run via:

    uv run python scripts/tier2_eval_r2.py --output notes/T2R2.4_evaluation.md

The eval is read-only — uses `Corpus(read_only=True)` and does not
modify the DuckDB store.
"""

from __future__ import annotations

import argparse
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml

# Local imports
from bb_lab.corpus import Corpus
from bb_lab.group import ZmZn
from bb_lab.poly import Poly

# Import the candidates and harness
sys.path.insert(0, str(Path(__file__).resolve().parent))
from tier2_candidates_r2 import (  # noqa: E402
    R2_CANDIDATES,
    evaluate_lower_bound,
)


# ===========================================================================
# Bravyi-table evaluation
# ===========================================================================


def _load_bravyi_table() -> list[dict]:
    """Load the Bravyi reference instances from
    `instances/bravyi_table.yaml`."""
    path = (
        Path(__file__).resolve().parent.parent
        / "instances" / "bravyi_table.yaml"
    )
    with open(path) as f:
        data = yaml.safe_load(f)
    return data["instances"]


def _row_dict_from_bravyi(inst: dict, extra_features: dict | None = None) -> dict:
    """Make a dict that looks like a corpus row for a Bravyi instance.
    Need to add: A_poly, B_poly, ell, m, n, k, d_exact, ...
    Also computes A_weight, B_weight, min_wt_ker_A, min_wt_ker_B,
    tanner_girth, dim_ker_A, dim_ker_B."""
    from bb_lab.checks import bb_check_matrices, circulant
    from bb_lab.features import min_weight_in_kernel, tanner_girth
    from bb_lab.linalg import nullspace_f2

    G = ZmZn(inst["group"]["ell"], inst["group"]["m"])
    A = Poly.from_string(inst["polynomials"]["A"], G)
    B = Poly.from_string(inst["polynomials"]["B"], G)
    n = inst["parameters"]["n"]
    k = inst["parameters"]["k"]
    d = inst["parameters"]["d"]

    M_A = circulant(A)
    M_B = circulant(B)
    dim_ker_A = nullspace_f2(M_A).shape[0]
    dim_ker_B = nullspace_f2(M_B).shape[0]

    row: dict[str, Any] = {
        "instance_id": inst["code_id"],
        "code_id": inst["code_id"],
        "group_struct": f"Z{G.orders[0]}xZ{G.orders[1]}",
        "ell": G.orders[0],
        "m": G.orders[1],
        "n": n,
        "k": k,
        "A_poly": A.canonical_string(),
        "B_poly": B.canonical_string(),
        "A_weight": A.weight(),
        "B_weight": B.weight(),
        "d_exact": d,
        "dim_ker_A": dim_ker_A,
        "dim_ker_B": dim_ker_B,
    }
    # Add minimum weight features only if kernel is brute-forceable.
    # bb_288 has dim_ker = 24; we use the Bravyi-table d for known min_wt
    # values, where applicable, since min_wt_ker = d for bb_288 (per
    # Bravyi 24: d_X = 18, min_wt_ker_A = ?). We DON'T know min_wt_ker
    # for bb_288 a priori, so leave it as None and the candidate will skip.
    if dim_ker_A <= 22:
        row["min_wt_ker_A"] = min_weight_in_kernel(M_A)
    else:
        row["min_wt_ker_A"] = None
    if dim_ker_B <= 22:
        row["min_wt_ker_B"] = min_weight_in_kernel(M_B)
    else:
        row["min_wt_ker_B"] = None
    # Tanner girth is cheap
    checks = bb_check_matrices(A, B)
    girth = tanner_girth(checks.H_X)
    if girth == float("inf"):
        row["tanner_girth"] = 999  # sentinel for "no cycle"
    else:
        row["tanner_girth"] = int(girth)
    if extra_features:
        row.update(extra_features)
    return row


def _bravyi_evaluate_candidate(cand, instances: list[dict]) -> list[dict]:
    """Compute the bound on each Bravyi instance, return summary rows."""
    out = []
    for inst in instances:
        try:
            row = _row_dict_from_bravyi(inst)
            # Sanity: skip if required column is None
            if any(row.get(c) is None for c in cand.requires):
                out.append({
                    "code_id": inst["code_id"],
                    "d_exact": row["d_exact"],
                    "bound": None,
                    "status": "skipped",
                    "reason": f"required col is None: {cand.requires}",
                })
                continue
            bound = int(cand.bound_fn(row))
            d = row["d_exact"]
            if bound > d:
                status = "VIOLATION"
            elif bound == d:
                status = "tight"
            else:
                status = "loose"
            out.append({
                "code_id": inst["code_id"],
                "d_exact": d, "bound": bound, "status": status,
                "looseness": d - bound,
            })
        except Exception as e:
            out.append({
                "code_id": inst["code_id"],
                "d_exact": inst["parameters"]["d"],
                "bound": None,
                "status": "error",
                "reason": str(e),
            })
    return out


# ===========================================================================
# Report formatting
# ===========================================================================


def _format_corpus_report(reports: list[dict]) -> list[str]:
    out: list[str] = []
    out.append("## Corpus evaluation (per candidate)")
    out.append("")
    out.append("| Candidate | Applicable | Tight | Tight % | Violations | Violation % | Min looseness | Mean looseness | Max looseness |")
    out.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for r in reports:
        if "note" in r:
            out.append(
                f"| {r['name']} | 0 | - | - | - | - | - | - | - |"
            )
            continue
        out.append(
            f"| {r['name']} | {r['applicable_rows']} | "
            f"{r['tight_count']} | {r['tight_rate']*100:.1f}% | "
            f"{r['violations_count']} | "
            f"{r['violation_rate']*100:.2f}% | "
            f"{r['min_looseness']} | {r['mean_looseness']:.2f} | "
            f"{r['max_looseness']} |"
        )
    out.append("")
    for r in reports:
        if "note" in r:
            continue
        out.append(f"### Per-candidate detail: `{r['name']}`")
        out.append(f"- **Formula:** `{r['formula']}`")
        out.append(f"- **Citation:** {r['citation']}")
        out.append(
            f"- Applicable rows: **{r['applicable_rows']}**  "
            f"(tight: {r['tight_count']}; "
            f"violations: {r['violations_count']})"
        )
        if r["violations_count"] > 0:
            out.append("")
            out.append("**Violations (sampled):**")
            out.append("")
            out.append("| Row | Group | n | k | d_exact | bound | Violates by | A | B |")
            out.append("|---|---|---:|---:|---:|---:|---:|---|---|")
            for v in r["violations"][:5]:
                if "error" in v:
                    out.append(f"| {v['row'][:8]} | error: {v['error']} | | | | | | | |")
                else:
                    out.append(
                        f"| {v['row'][:8]} | {v['group']} | "
                        f"{v['n']} | {v['k']} | {v['d_exact']} | "
                        f"{v['bound']} | +{v['bound']-v['d_exact']} | "
                        f"`{v['A_poly']}` | `{v['B_poly']}` |"
                    )
            out.append("")
        if r["per_group_violations"]:
            out.append("**Per-group violation counts:**")
            for g in sorted(r["per_group_violations"]):
                out.append(
                    f"- `{g}`: {r['per_group_violations'][g]} violations"
                )
            out.append("")
        out.append("**Per-group tightness:**")
        for g in sorted(r["per_group_tight"]):
            tight, total = r["per_group_tight"][g]
            out.append(
                f"- `{g}`: {tight}/{total} tight ({tight/max(total,1)*100:.1f}%)"
            )
        out.append("")
    return out


def _format_bravyi_report(
    cand_results: dict[str, list[dict]],
) -> list[str]:
    out: list[str] = []
    out.append("## Bravyi-table evaluation")
    out.append("")
    out.append("Reference instances from `instances/bravyi_table.yaml`. "
               "Critical: the gross instance `[[144,12,12]]` is the headline "
               "tightness benchmark.")
    out.append("")
    out.append("| Candidate | bb_72_12_6 (d=6) | bb_90_8_10 (d=10) | bb_108_8_10 (d=10) | gross (d=12) | bb_288_12_18 (d=18) |")
    out.append("|---|---|---|---|---|---|")
    cand_order = list(cand_results.keys())
    for cn in cand_order:
        row_vals = []
        for inst_id in ["bb_72_12_6", "bb_90_8_10", "bb_108_8_10", "gross", "bb_288_12_18"]:
            matches = [r for r in cand_results[cn] if r["code_id"] == inst_id]
            if not matches:
                row_vals.append("—")
                continue
            m = matches[0]
            if m["status"] == "skipped" or m["status"] == "error":
                reason = m.get("reason", "?")[:40]
                row_vals.append(f"_{m['status']}_ ({reason})")
            elif m["bound"] is None:
                row_vals.append("—")
            elif m["status"] == "VIOLATION":
                row_vals.append(
                    f"**VIOLATION** bound={m['bound']} > d={m['d_exact']}"
                )
            elif m["status"] == "tight":
                row_vals.append(f"**TIGHT** bound={m['bound']}")
            else:
                row_vals.append(f"bound={m['bound']} (loose by {m['looseness']})")
        out.append(
            f"| `{cn}` | " + " | ".join(row_vals) + " |"
        )
    out.append("")
    return out


# ===========================================================================
# Main driver
# ===========================================================================


def main() -> None:
    ap = argparse.ArgumentParser(
        description=(
            "Tier-2 Round 2 candidate evaluation. Reads the corpus + "
            "Bravyi table, computes bounds, writes a markdown report."
        ),
    )
    ap.add_argument(
        "--db", type=Path, default=None,
        help="Path to bb_instances.duckdb (default: lab's).",
    )
    ap.add_argument(
        "--groups", nargs="*", default=None,
        help="Restrict corpus eval to these group_struct labels.",
    )
    ap.add_argument(
        "--output", "-o", type=Path,
        default=Path("notes/T2R2.4_evaluation.md"),
        help="Where to write the markdown report.",
    )
    ap.add_argument(
        "--limit", type=int, default=None,
        help="For smoke testing: limit corpus rows.",
    )
    ap.add_argument(
        "--corpus-only", action="store_true",
        help="Skip the Bravyi-table benchmark.",
    )
    args = ap.parse_args()

    corpus = Corpus(db_path=args.db) if args.db else Corpus()
    summary = corpus.summary()
    print(f"corpus: {summary}", file=sys.stderr)

    if args.limit is not None:
        corpus = corpus.limited(int(args.limit))

    # === Corpus eval ===
    print(f"\nEvaluating {len(R2_CANDIDATES)} candidates on corpus...", file=sys.stderr)
    reports = []
    for cand in R2_CANDIDATES:
        t0 = time.time()
        print(f"  {cand.name}...", end=" ", flush=True, file=sys.stderr)
        rep = evaluate_lower_bound(corpus, cand, args.groups)
        reports.append(rep)
        print(f"({time.time()-t0:.1f}s)", file=sys.stderr)

    # === Bravyi eval ===
    bravyi_results: dict[str, list[dict]] = {}
    if not args.corpus_only:
        instances = _load_bravyi_table()
        print(
            f"\nEvaluating {len(R2_CANDIDATES)} candidates on "
            f"{len(instances)} Bravyi-table instances...",
            file=sys.stderr,
        )
        for cand in R2_CANDIDATES:
            t0 = time.time()
            print(f"  {cand.name}...", end=" ", flush=True, file=sys.stderr)
            bravyi_results[cand.name] = _bravyi_evaluate_candidate(cand, instances)
            print(f"({time.time()-t0:.1f}s)", file=sys.stderr)

    # === Format report ===
    lines: list[str] = []
    lines.append("# T2R2.4 — Candidate evaluation results")
    lines.append("")
    lines.append("Generated by `scripts/tier2_eval_r2.py`.")
    lines.append("")
    lines.append(
        "**Corpus summary**: " + ", ".join(
            f"{k}={v}" for k, v in summary.items()
        )
    )
    lines.append("")
    lines.append("## Methodology")
    lines.append("")
    lines.append(
        "Each candidate is evaluated as a LOWER bound: `bound ≤ d_exact` "
        "is the desired direction. A row is:"
    )
    lines.append("- **tight** if `bound == d_exact`")
    lines.append("- **loose** if `bound < d_exact`")
    lines.append(
        "- **VIOLATION** if `bound > d_exact` — falsifies the candidate"
    )
    lines.append("")

    lines.extend(_format_corpus_report(reports))

    if not args.corpus_only:
        lines.extend(_format_bravyi_report(bravyi_results))

    # === Summary verdict ===
    lines.append("## Summary verdict")
    lines.append("")
    lines.append("| Candidate | Verdict | Gross tightness |")
    lines.append("|---|---|---|")
    for rep, cn in zip(reports, [c.name for c in R2_CANDIDATES]):
        if "note" in rep:
            verdict = "n/a"
        elif rep["violations_count"] > 0:
            verdict = f"**FALSIFIED** ({rep['violations_count']} violations)"
        elif rep["tight_count"] > 0:
            verdict = f"survives, {rep['tight_count']} tight"
        else:
            verdict = "survives, never tight"

        gross_str = "—"
        if cn in bravyi_results:
            gm = [r for r in bravyi_results[cn] if r["code_id"] == "gross"]
            if gm:
                m = gm[0]
                if m.get("bound") is not None:
                    if m["status"] == "tight":
                        gross_str = f"**TIGHT** ({m['bound']})"
                    elif m["status"] == "VIOLATION":
                        gross_str = f"**VIOLATION** ({m['bound']} > {m['d_exact']})"
                    else:
                        gross_str = f"bound={m['bound']} (d=12, loose by {m['looseness']})"
                else:
                    gross_str = f"_{m['status']}_"
        lines.append(f"| `{cn}` | {verdict} | {gross_str} |")
    lines.append("")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    print(f"\nReport written to {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()

"""Tier-2 Round 3 evaluation: HT/Roos bound on BB codes.

Computes mv_ht(T_A), mv_ht(T_B), and the composite single-block-
dominance bound bb_ht_bound(A, B, G) over the corpus AND the 5
reference Bravyi codes, then reports:

  * tightness and violation rates conditioned on `S(A, B)` (the
    textbook-CSS-upper-bound-tight regime), and
  * the per-Bravyi-code table for the gross-instance benchmark.

Outputs `notes/T2R3.4_eval.md`. Read-only DuckDB access; no schema
changes.

Usage::

    cd experiments/bb_lab
    uv run python scripts/tier2_ht_roos_eval.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

import yaml

from bb_lab.algebraic_features import _g_odd_orders
from bb_lab.checks import circulant
from bb_lab.corpus import Corpus
from bb_lab.features import min_weight_in_kernel
from bb_lab.group import ZmZn
from bb_lab.ht_roos import (
    bb_ht_bound,
    bb_ht_condition,
    bb_ht_per_block_bound,
    defining_set,
    mv_ht_bound,
    nonvanishing_set,
)
from bb_lab.poly import Poly


# Hard limit on per-block kernel enumeration. Above this, skip the row
# (rows with d_A^⊥ unknown are reported separately).
MAX_KERNEL_DIM = 22


def _eval_row(row: dict[str, Any]) -> dict[str, Any]:
    """Compute the HT/Roos bound + condition for a single corpus row.

    Returns a dict with the inputs and computed values; missing /
    skipped fields are None.
    """
    out: dict[str, Any] = {
        "instance_id": row["instance_id"][:8],
        "group_struct": row["group_struct"],
        "n": row["n"],
        "k": row["k"],
        "A_poly": row["A_poly"],
        "B_poly": row["B_poly"],
        "d_exact": row["d_exact"],
        "min_wt_ker_A": row["min_wt_ker_A"],
        "min_wt_ker_B": row["min_wt_ker_B"],
        "mv_ht_A": None,
        "mv_ht_B": None,
        "bb_ht_bound": None,
        "bb_ht_condition_ok": None,
        "bb_ht_condition_diag": None,
        "violation": None,  # True if bound > d_exact (only relevant when condition holds)
    }
    if row["A_poly"] is None or row["B_poly"] is None:
        out["bb_ht_condition_diag"] = "no_poly"
        return out
    ell = row["ell"]
    m = row["m"]
    G = ZmZn(ell, m)
    try:
        A = Poly.from_string(row["A_poly"], G)
        B = Poly.from_string(row["B_poly"], G)
    except Exception as e:
        out["bb_ht_condition_diag"] = f"poly_parse_error:{e}"
        return out

    n_odds = _g_odd_orders(G)
    # HT applied to the nonvanishing set of A gives a lower bound on
    # d_A^⊥ = d(ker M_A). See `ht_roos.nonvanishing_set` doc for why.
    nv_A = nonvanishing_set(A, G)
    nv_B = nonvanishing_set(B, G)
    ht_a = mv_ht_bound(nv_A, n_odds)
    ht_b = mv_ht_bound(nv_B, n_odds)
    out["mv_ht_A"] = ht_a
    out["mv_ht_B"] = ht_b

    ok, diag = bb_ht_condition(
        A, B, G, d_exact=row["d_exact"], max_kernel_dim=MAX_KERNEL_DIM
    )
    out["bb_ht_condition_ok"] = ok
    out["bb_ht_condition_diag"] = diag
    if ok:
        bound = min(ht_a, ht_b)
    else:
        bound = 1
    out["bb_ht_bound"] = bound
    if row["d_exact"] is not None and ok:
        out["violation"] = bound > row["d_exact"]
    return out


def evaluate_bravyi() -> list[dict[str, Any]]:
    """Evaluate the 5 reference Bravyi instances from
    `instances/bravyi_table.yaml`. Skip rows where the per-block kernel
    is too big.
    """
    bravyi_path = ROOT / "instances" / "bravyi_table.yaml"
    with open(bravyi_path) as f:
        table = yaml.safe_load(f)
    results: list[dict[str, Any]] = []
    for inst in table["instances"]:
        ell = inst["group"]["ell"]
        m = inst["group"]["m"]
        G = ZmZn(ell, m)
        A = Poly.from_string(inst["polynomials"]["A"], G)
        B = Poly.from_string(inst["polynomials"]["B"], G)
        code_id = inst["code_id"]
        actual_d = inst["parameters"]["d"]
        n_odds = _g_odd_orders(G)
        nv_A = nonvanishing_set(A, G)
        nv_B = nonvanishing_set(B, G)
        ht_a = mv_ht_bound(nv_A, n_odds)
        ht_b = mv_ht_bound(nv_B, n_odds)

        # For Bravyi we need d_A^⊥, d_B^⊥. For bb_288 (|G|=144) brute force
        # is infeasible; report whichever is computable.
        M_A = circulant(A)
        M_B = circulant(B)
        try:
            d_A_perp = min_weight_in_kernel(M_A)
        except ValueError:
            d_A_perp = None
        try:
            d_B_perp = min_weight_in_kernel(M_B)
        except ValueError:
            d_B_perp = None

        if d_A_perp is not None and d_B_perp is not None:
            ok, diag = bb_ht_condition(A, B, G, d_exact=actual_d)
        else:
            ok, diag = (False, "block_kernel_too_big")

        bound = min(ht_a, ht_b) if ok else 1
        violation = (bound > actual_d) if (actual_d is not None and ok) else None
        results.append(
            {
                "code_id": code_id,
                "n": inst["parameters"]["n"],
                "k": inst["parameters"]["k"],
                "d": actual_d,
                "mv_ht_A": ht_a,
                "mv_ht_B": ht_b,
                "d_A_perp": d_A_perp,
                "d_B_perp": d_B_perp,
                "min_d_perp": (
                    min(d_A_perp, d_B_perp)
                    if d_A_perp is not None and d_B_perp is not None
                    else None
                ),
                "condition_ok": ok,
                "condition_diag": diag,
                "bb_ht_bound": bound,
                "violation": violation,
                "loose_by": (
                    actual_d - bound if (ok and actual_d is not None) else None
                ),
            }
        )
    return results


def evaluate_corpus(*, limit: int | None = None) -> list[dict[str, Any]]:
    """Evaluate the HT/Roos bound across all corpus rows with d_exact.

    Optional `limit` caps the number of rows (for quick smoke-test).
    """
    c = Corpus()
    rows_iter = c.filter(d_exact_is_not_null=True)
    if limit:
        rows_iter = rows_iter.limited(limit)
    rows_dicts = list(rows_iter)  # iterates dicts
    results: list[dict[str, Any]] = []
    for r in rows_dicts:
        results.append(_eval_row(r))
    return results


def summarize_corpus(results: list[dict[str, Any]]) -> dict[str, Any]:
    """Compute summary stats over the corpus eval."""
    n_total = len(results)
    n_skipped = sum(
        1
        for r in results
        if r["bb_ht_condition_diag"]
        in ("no_poly", "poly_parse_error", "block_kernel_too_big", "joint_kernel_too_big")
    )
    n_condition_holds = sum(1 for r in results if r["bb_ht_condition_ok"])
    n_condition_fails = sum(
        1 for r in results if r["bb_ht_condition_ok"] is False
    )
    n_violations = sum(1 for r in results if r.get("violation"))
    n_tight = sum(
        1
        for r in results
        if r["bb_ht_condition_ok"]
        and r["d_exact"] is not None
        and r["bb_ht_bound"] == r["d_exact"]
    )
    # Per-group breakdown
    by_group: dict[str, dict[str, int]] = {}
    for r in results:
        g = r["group_struct"] or "?"
        bucket = by_group.setdefault(
            g,
            {
                "total": 0,
                "condition_holds": 0,
                "tight": 0,
                "violations": 0,
            },
        )
        bucket["total"] += 1
        if r["bb_ht_condition_ok"]:
            bucket["condition_holds"] += 1
            if r["d_exact"] is not None and r["bb_ht_bound"] == r["d_exact"]:
                bucket["tight"] += 1
            if r.get("violation"):
                bucket["violations"] += 1
    diag_counts: dict[str, int] = {}
    for r in results:
        d = r["bb_ht_condition_diag"] or "?"
        diag_counts[d] = diag_counts.get(d, 0) + 1
    return {
        "n_total": n_total,
        "n_skipped": n_skipped,
        "n_condition_holds": n_condition_holds,
        "n_condition_fails": n_condition_fails,
        "n_violations": n_violations,
        "n_tight_in_S": n_tight,
        "diag_counts": diag_counts,
        "by_group": by_group,
    }


def write_note(
    bravyi: list[dict[str, Any]],
    corpus_results: list[dict[str, Any]],
    summary: dict[str, Any],
    out_path: Path,
) -> None:
    """Write the T2R3.4 evaluation note in markdown."""
    lines: list[str] = []
    lines.append("# T2R3.4 — HT/Roos bound evaluation\n")
    lines.append(
        "Generated by `scripts/tier2_ht_roos_eval.py`. This evaluates the\n"
        "candidate single-block-dominance lower bound\n\n"
        "```\n"
        "d_X(BB(A, B))  ≥  min(mv_ht(T_A), mv_ht(T_B))  when S(A, B) holds\n"
        "```\n\n"
        "where `T_A, T_B ⊆ Ĝ_odd` are the defining sets of the per-block\n"
        "cyclic codes, `mv_ht(·)` is the multivariate Hartmann–Tzeng bound,\n"
        "and `S(A, B)` is the structural condition\n\n"
        "    S(A, B)  :=  d_X = min(d_A^⊥, d_B^⊥)    (textbook CSS upper bound is tight)\n\n"
        "verified per-row against the corpus's `d_exact`.\n\n"
    )

    # --- Bravyi table ------------------------------------------------------
    lines.append("## 1. Bravyi-table evaluation\n\n")
    lines.append(
        "| code | n | k | d | mv_ht(T_A) | mv_ht(T_B) | d_A^⊥ | d_B^⊥ | S(A,B)? | bb_ht_bound | loose by |\n"
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n"
    )
    for r in bravyi:
        s_str = "yes" if r["condition_ok"] else f"no ({r['condition_diag']})"
        d_a = r["d_A_perp"] if r["d_A_perp"] is not None else "?"
        d_b = r["d_B_perp"] if r["d_B_perp"] is not None else "?"
        loose = r["loose_by"] if r["loose_by"] is not None else "—"
        lines.append(
            f"| {r['code_id']} | {r['n']} | {r['k']} | {r['d']} | "
            f"{r['mv_ht_A']} | {r['mv_ht_B']} | {d_a} | {d_b} | {s_str} | "
            f"{r['bb_ht_bound']} | {loose} |\n"
        )
    lines.append("\n")

    # --- Gross-specific verdict ------------------------------------------
    gross_row = next((r for r in bravyi if r["code_id"] == "gross"), None)
    if gross_row is not None:
        lines.append("### Gross-specific verdict\n\n")
        lines.append(
            f"- `mv_ht(T_A) = {gross_row['mv_ht_A']}`, "
            f"`mv_ht(T_B) = {gross_row['mv_ht_B']}` "
            f"(actual `d = {gross_row['d']}`).\n"
        )
        lines.append(
            f"- Structural condition `S(A, B)` "
            f"{'holds' if gross_row['condition_ok'] else 'does NOT hold'}: "
            f"`{gross_row['condition_diag']}`.\n"
        )
        if gross_row["condition_ok"]:
            lines.append(
                f"- `bb_ht_bound = {gross_row['bb_ht_bound']}`, "
                f"loose by `{gross_row['loose_by']}` "
                f"({'matches' if gross_row['loose_by'] == 0 else 'does NOT match'} "
                f"the engineering target `d = 12`).\n"
            )
        else:
            diag = gross_row["condition_diag"]
            if diag == "G_not_semisimple":
                lines.append(
                    "- The condition fails because `F_2[G] is not semisimple` "
                    "for gross's `G = Z_12 × Z_6` (`|G| = 72`, even). "
                    "HT/Roos applies to the semisimple-quotient F_2[G_odd] = "
                    "F_2[Z_3 × Z_3]; the Jacobson radical of F_2[G] "
                    "contributes additional kernel mass that the HT bound "
                    "cannot see. Furthermore, G_odd = Z_3 × Z_3 is "
                    "non-cyclic (gcd(3,3) = 3), so no full-G_odd generator "
                    "exists — the brute-force multivariate HT step search "
                    "also returns 1 there. Both obstructions point at the "
                    "same structural issue: BB codes' engineered G shapes "
                    "(per HANDOFF §6i) lie outside the regime where simple "
                    "cyclic-code algebra gives tight bounds.\n"
                )
            elif diag == "block_kernel_too_big":
                lines.append(
                    "- Skipped: per-block kernel too large for brute-force "
                    "enumeration (dim > 22).\n"
                )
            else:
                lines.append(
                    f"- The condition fails with diagnostic `{diag}`.\n"
                )
        lines.append("\n")

    # --- Corpus eval summary --------------------------------------------
    lines.append("## 2. Corpus evaluation summary\n\n")
    lines.append(f"- **Total rows evaluated**: {summary['n_total']}\n")
    lines.append(f"- **Skipped (kernel too big / no poly)**: {summary['n_skipped']}\n")
    lines.append(
        f"- **Condition `S(A, B)` holds**: {summary['n_condition_holds']} "
        f"({100 * summary['n_condition_holds'] / max(1, summary['n_total']):.1f}%)\n"
    )
    lines.append(
        f"- **Condition fails**: {summary['n_condition_fails']} "
        f"({100 * summary['n_condition_fails'] / max(1, summary['n_total']):.1f}%)\n"
    )
    lines.append(
        f"- **Violations (`bb_ht_bound > d_exact`, condition holds)**: "
        f"{summary['n_violations']}\n"
    )
    lines.append(
        f"- **Tight (`bb_ht_bound == d_exact`, condition holds)**: "
        f"{summary['n_tight_in_S']}\n"
    )
    lines.append("\n")

    lines.append("### 2a. Per-condition-diagnostic counts\n\n")
    lines.append("| diagnostic | count |\n|---|---:|\n")
    for d, c in sorted(summary["diag_counts"].items(), key=lambda x: -x[1]):
        lines.append(f"| `{d}` | {c} |\n")
    lines.append("\n")

    lines.append("### 2b. Per-group breakdown\n\n")
    lines.append(
        "| group | total | S holds | tight (in S) | violations |\n|---|---:|---:|---:|---:|\n"
    )
    for g, b in sorted(summary["by_group"].items()):
        lines.append(
            f"| {g} | {b['total']} | {b['condition_holds']} | "
            f"{b['tight']} | {b['violations']} |\n"
        )
    lines.append("\n")

    # --- Verdict --------------------------------------------------------
    lines.append("## 3. Verdict\n\n")
    has_violations = summary["n_violations"] > 0
    gross_tight = (
        gross_row is not None
        and gross_row["condition_ok"]
        and gross_row["loose_by"] == 0
    )
    if has_violations:
        verdict = "FALSIFIED"
    elif gross_tight:
        verdict = "survives-tight-on-gross"
    elif gross_row is not None and not gross_row["condition_ok"]:
        verdict = "survives-loose-on-gross-condition-fails"
    elif gross_row is not None and gross_row["condition_ok"]:
        verdict = "survives-loose-on-gross"
    else:
        verdict = "inconclusive"
    lines.append(f"**Verdict**: `{verdict}`.\n\n")

    # Footer
    lines.append(
        "_Generated by `scripts/tier2_ht_roos_eval.py` on the corpus snapshot.\n"
        "Re-run after corpus changes to update._\n"
    )
    out_path.write_text("".join(lines))
    print(f"Wrote {out_path}")


def main() -> int:
    print("Evaluating Bravyi instances ...", flush=True)
    bravyi = evaluate_bravyi()
    print("Bravyi results:")
    for r in bravyi:
        print(json.dumps(r, default=str, indent=2))
    print("\nEvaluating corpus ...", flush=True)
    corpus_results = evaluate_corpus()
    print(f"Corpus rows evaluated: {len(corpus_results)}")
    summary = summarize_corpus(corpus_results)
    print(f"Summary: {json.dumps(summary, indent=2, default=str)}")

    out_path = ROOT / "notes" / "T2R3.4_eval.md"
    write_note(bravyi, corpus_results, summary, out_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())

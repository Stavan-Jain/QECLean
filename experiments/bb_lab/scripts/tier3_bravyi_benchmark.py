"""Tier-3 Bravyi-table benchmark.

Compute the Jacobson-radical bound on all five Bravyi BB codes:
  * [[72, 12, 6]]
  * [[90, 8, 10]]
  * [[108, 8, 10]]
  * [[144, 12, 12]] gross
  * [[288, 12, 18]]

Tabulate bound vs. published d for each. The gross tightness is the
headline test per the Tier-3 spec.
"""

from __future__ import annotations

from pathlib import Path

import yaml

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_depth,
    jacobson_radical_bound,
)
from bb_lab.group import ZmZn
from bb_lab.poly import Poly


def main(out: Path | None = None):
    bravyi_path = Path(__file__).resolve().parent.parent / "instances" / "bravyi_table.yaml"
    bravyi_data = yaml.safe_load(bravyi_path.read_text())

    lines: list[str] = []
    lines.append("# T3.3 — Bravyi-table benchmark of the Jacobson-radical conjecture")
    lines.append("")
    lines.append(
        "Bound:  d_X  ≥  Σ_{O ∈ V_A ∩ V_B}  |O| · min(μ_O(A), μ_O(B))"
    )
    lines.append("")
    lines.append("## Headline table")
    lines.append("")
    lines.append("| code | group | A | B | published d | bound | gap (d - bound) | tight? |")
    lines.append("|---|---|---|---|---:|---:|---:|:---:|")

    rows: list[dict] = []
    for inst in bravyi_data["instances"]:
        ell = inst["group"]["ell"]
        m = inst["group"]["m"]
        G = ZmZn(ell, m)
        A = Poly.from_string(inst["polynomials"]["A"], G)
        B = Poly.from_string(inst["polynomials"]["B"], G)
        d_published = inst["parameters"]["d"]
        bound = jacobson_radical_bound(A, B, G)
        gap = d_published - bound
        is_violation = gap < 0
        is_tight = gap == 0
        tight_str = "YES" if is_tight else ("VIOLATION" if is_violation else "no")
        rows.append(dict(
            code_id=inst["code_id"],
            group=G.label(),
            A=inst["polynomials"]["A"],
            B=inst["polynomials"]["B"],
            d=d_published,
            bound=bound,
            gap=gap,
            tight=is_tight,
            violation=is_violation,
        ))
        lines.append(
            f"| {inst['code_id']} | {G.label()} | "
            f"`{inst['polynomials']['A']}` | `{inst['polynomials']['B']}` | "
            f"{d_published} | {bound} | {gap} | {tight_str} |"
        )

    lines.append("")
    lines.append("## Per-code orbit detail")
    lines.append("")
    for inst, row in zip(bravyi_data["instances"], rows):
        ell = inst["group"]["ell"]
        m = inst["group"]["m"]
        G = ZmZn(ell, m)
        A = Poly.from_string(inst["polynomials"]["A"], G)
        B = Poly.from_string(inst["polynomials"]["B"], G)
        orbits = g_odd_frobenius_orbits(G)
        lines.append(f"### {inst['display_name']}  (G = {G.label()}, "
                     f"|G|={G.cardinality}, G_odd = {len(orbits)} orbits)")
        lines.append("")
        lines.append("| orbit (G_odd rep) | |O| | μ(A) | μ(B) | contribution |")
        lines.append("|---|---:|---:|---:|---:|")
        total = 0
        for o in orbits:
            mu_A = jacobson_radical_depth(A, o, G)
            mu_B = jacobson_radical_depth(B, o, G)
            contrib = len(o) * min(mu_A, mu_B) if mu_A > 0 and mu_B > 0 else 0
            total += contrib
            rep = sorted(o)[0]
            lines.append(f"| {rep} (full: {sorted(o)[:3]}...) | {len(o)} | "
                         f"{mu_A} | {mu_B} | {contrib} |")
        lines.append(f"| **TOTAL** | | | | **{total}** |")
        lines.append("")
        lines.append(f"  Published d = {inst['parameters']['d']}; bound = {row['bound']}; "
                     f"gap = {row['gap']}.")
        lines.append("")

    # Summary
    lines.append("## Summary")
    lines.append("")
    n_total = len(rows)
    n_tight = sum(1 for r in rows if r["tight"])
    n_violations = sum(1 for r in rows if r["violation"])
    lines.append(f"- Total Bravyi codes: {n_total}")
    lines.append(f"- Tight: {n_tight}")
    lines.append(f"- Violations: {n_violations}")
    lines.append(f"- Loose (but valid): {n_total - n_tight - n_violations}")
    lines.append("")
    gross_row = next(r for r in rows if r["code_id"] == "gross")
    lines.append(f"- **Gross headline**: published d=12, bound={gross_row['bound']}, "
                 f"gap={gross_row['gap']}, {'TIGHT' if gross_row['tight'] else 'NOT TIGHT'}.")
    if n_violations > 0:
        lines.append("")
        lines.append("**VIOLATIONS found on Bravyi-table codes — strong falsification.**")

    report = "\n".join(lines)
    if out:
        out.write_text(report)
        print(f"Wrote report to {out}")
    else:
        print(report)


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=None)
    args = ap.parse_args()
    main(args.output)

"""T2R5.3 — Evaluate the SRB 2025 cover-graph chain-map bound across:

  * The 5 Bravyi-table BB instances (full table).
  * The full corpus (`bb_instances.duckdb`) with `d_exact IS NOT NULL`.

Outputs:

  * A console summary table for Bravyi.
  * A console summary of corpus statistics (rows, violations, tightness).
  * `notes/T2R5.3_eval.md` written with the same numbers in markdown
    form, plus a per-group breakdown.

Read-only on the corpus DB.

Usage::

    uv run python scripts/tier2_homological_eval.py
"""

from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path
from typing import Callable

import yaml

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.corpus import Corpus
from bb_lab.group import AbelianGroup, ZmZn
from bb_lab.homological_bounds import (
    bb_homological_bound,
    bb_homological_condition,
    bb_homological_upper_bound,
    enumerate_base_codes,
)
from bb_lab.poly import Poly


# ---------------------------------------------------------------------------
# Base-distance lookup: dynamically backed by the corpus + Bravyi table
# ---------------------------------------------------------------------------


def _load_bravyi_table() -> list[dict]:
    """Load the 5 reference instances from `instances/bravyi_table.yaml`."""
    path = LAB_ROOT / "instances" / "bravyi_table.yaml"
    data = yaml.safe_load(path.read_text())
    return data["instances"]


def _parse_bravyi_polys(row: dict) -> tuple[Poly, Poly, AbelianGroup]:
    """Convert a Bravyi-row dict into `(A, B, G)`."""
    g = row["group"]
    G = ZmZn(g["ell"], g["m"])
    A = Poly.from_string(row["polynomials"]["A"], G)
    B = Poly.from_string(row["polynomials"]["B"], G)
    return A, B, G


class _CorpusBackedLookup:
    """`base_distance` callable that resolves `(A, B, G)` against
    the corpus DB and the Bravyi table.

    Cached so the corpus is queried once per unique `(canonical_string)`
    triple in a sweep.
    """

    def __init__(self) -> None:
        self._cache: dict[tuple[tuple[int, ...], str, str], int | None] = {}
        # Bravyi table is the primary in-memory cache:
        self._bravyi_lookup: dict[tuple[tuple[int, ...], str, str], int] = {}
        for row in _load_bravyi_table():
            A, B, G = _parse_bravyi_polys(row)
            key = (G.orders, A.canonical_string(), B.canonical_string())
            self._bravyi_lookup[key] = int(row["parameters"]["d"])
            # And the symmetric (B, A) key, in case the cover/base
            # projection swaps them — actually SRB doesn't swap, so
            # we keep the canonical (A, B) order.

    def __call__(
        self, A: Poly, B: Poly, G: AbelianGroup,
    ) -> int | None:
        key = (G.orders, A.canonical_string(), B.canonical_string())
        if key in self._bravyi_lookup:
            return self._bravyi_lookup[key]
        if key in self._cache:
            return self._cache[key]
        # Query corpus: find any row matching this exact (G, A, B).
        A_str = A.canonical_string()
        B_str = B.canonical_string()
        group_label = G.label()
        rows = (
            Corpus()
            .filter(
                group_struct=group_label,
                A_poly=A_str,
                B_poly=B_str,
                d_exact_is_not_null=True,
            )
            .column("d_exact")
        )
        if rows:
            d = int(rows[0])
            self._cache[key] = d
            return d
        # Try swapping A and B — Aut(G)-orbit may have swapped them.
        rows_swap = (
            Corpus()
            .filter(
                group_struct=group_label,
                A_poly=B_str,
                B_poly=A_str,
                d_exact_is_not_null=True,
            )
            .column("d_exact")
        )
        if rows_swap:
            d = int(rows_swap[0])
            self._cache[key] = d
            return d
        self._cache[key] = None
        return None


# ---------------------------------------------------------------------------
# Bravyi-table evaluation
# ---------------------------------------------------------------------------


def evaluate_bravyi_table(lookup: _CorpusBackedLookup) -> list[dict]:
    """Compute the homological bound for each of the 5 Bravyi instances.

    Returns a list of dicts with keys:
      code_id, d_exact, lower_conj, lower_rig, upper_conj, S_conj, S_rig,
      n_bases, n_odd_h_bases, n_usable_bases, best_base
    """
    out: list[dict] = []
    for row in _load_bravyi_table():
        A, B, G = _parse_bravyi_polys(row)
        d_exact = int(row["parameters"]["d"])

        bases = enumerate_base_codes(A, B, G)
        n_odd_h = sum(1 for b in bases if b.is_rigorous)
        usable: list = []
        for b in bases:
            d_base = lookup(b.A_base, b.B_base, b.G_base)
            if d_base is not None and d_base > 1:
                usable.append((b, d_base))

        best_usable = None
        if usable:
            best_usable = max(usable, key=lambda x: x[1])

        lower_conj = bb_homological_bound(A, B, G, base_distance=lookup)
        lower_rig = bb_homological_bound(
            A, B, G, base_distance=lookup, require_rigorous=True
        )
        upper_conj = bb_homological_upper_bound(A, B, G, base_distance=lookup)

        S_conj_ok, _ = bb_homological_condition(A, B, G, base_distance=lookup)
        S_rig_ok, _ = bb_homological_condition(
            A, B, G, base_distance=lookup, require_rigorous=True
        )

        out.append({
            "code_id": row["code_id"],
            "display_name": row["display_name"],
            "n": int(row["parameters"]["n"]),
            "k": int(row["parameters"]["k"]),
            "d_exact": d_exact,
            "lower_conj": lower_conj,
            "lower_rig": lower_rig,
            "upper_conj": upper_conj,
            "S_conj": S_conj_ok,
            "S_rig": S_rig_ok,
            "n_bases": len(bases),
            "n_odd_h_bases": n_odd_h,
            "n_usable_bases": len(usable),
            "best_base": (
                f"{best_usable[0].G_base.label()} d={best_usable[1]} h={best_usable[0].h}"
                if best_usable else "—"
            ),
        })
    return out


def print_bravyi_table(rows: list[dict]) -> None:
    print("\n=== Bravyi-table evaluation ===\n")
    header = (
        f"{'code_id':<14} {'n':>4} {'k':>3} {'d':>3} "
        f"{'S?':>5} {'lower':>6} {'upper':>6} "
        f"{'rig?':>5} {'rig_lo':>7} {'best_base':<30}"
    )
    print(header)
    print("-" * len(header))
    for r in rows:
        print(
            f"{r['code_id']:<14} {r['n']:>4} {r['k']:>3} {r['d_exact']:>3} "
            f"{'yes' if r['S_conj'] else 'no':>5} "
            f"{r['lower_conj']:>6} {r['upper_conj']:>6} "
            f"{'yes' if r['S_rig'] else 'no':>5} "
            f"{r['lower_rig']:>7} {r['best_base']:<30}"
        )


# ---------------------------------------------------------------------------
# Corpus sweep
# ---------------------------------------------------------------------------


def sweep_corpus(lookup: _CorpusBackedLookup) -> dict:
    """Sweep the entire labeled corpus (`d_exact IS NOT NULL`):

      • Count rows where S (conjectural) holds.
      • For those, check `bb_homological_bound ≤ d_exact` (lower bound
        should never exceed the exact distance — that would falsify
        the SRB conjecture).
      • Count violations.
      • Tightness rate: fraction of rows where bound = d_exact.
      • Per-group breakdown.

    Returns a dict with the headline numbers.
    """
    corpus = Corpus().filter(d_exact_is_not_null=True)
    n_labeled = corpus.count()

    n_rows = 0
    n_in_S_conj = 0
    n_in_S_rig = 0
    n_violations_conj = 0
    n_violations_rig = 0
    n_tight_conj = 0
    n_tight_rig = 0
    n_bound_gt1_conj = 0
    n_bound_gt1_rig = 0

    per_group_conj: Counter = Counter()        # rows
    per_group_in_S_conj: Counter = Counter()    # rows where S holds
    per_group_violations: Counter = Counter()   # rows where bound > d_exact
    per_group_tight: Counter = Counter()        # rows where bound = d_exact

    violation_examples: list[dict] = []

    for row in corpus:
        n_rows += 1
        group = row["group_struct"]
        per_group_conj[group] += 1
        d_exact = int(row["d_exact"])
        ell = int(row["ell"])
        m = int(row["m"])
        G = ZmZn(ell, m)
        try:
            A = Poly.from_string(row["A_poly"], G)
            B = Poly.from_string(row["B_poly"], G)
        except Exception as e:
            print(
                f"WARN: failed to parse poly for instance {row['instance_id']}: {e}"
            )
            continue

        lower_conj = bb_homological_bound(A, B, G, base_distance=lookup)
        lower_rig = bb_homological_bound(
            A, B, G, base_distance=lookup, require_rigorous=True
        )

        if lower_conj > 1:
            n_bound_gt1_conj += 1
        if lower_rig > 1:
            n_bound_gt1_rig += 1

        S_conj_ok = lower_conj > 1
        S_rig_ok = lower_rig > 1
        if S_conj_ok:
            n_in_S_conj += 1
            per_group_in_S_conj[group] += 1
            if lower_conj > d_exact:
                n_violations_conj += 1
                per_group_violations[group] += 1
                if len(violation_examples) < 10:
                    violation_examples.append({
                        "instance_id": row["instance_id"],
                        "code_id": row.get("code_id"),
                        "group_struct": group,
                        "n": int(row["n"]),
                        "k": int(row["k"]),
                        "d_exact": d_exact,
                        "lower_conj": lower_conj,
                        "A_poly": row["A_poly"],
                        "B_poly": row["B_poly"],
                    })
            elif lower_conj == d_exact:
                n_tight_conj += 1
                per_group_tight[group] += 1

        if S_rig_ok:
            n_in_S_rig += 1
            if lower_rig > d_exact:
                n_violations_rig += 1
            elif lower_rig == d_exact:
                n_tight_rig += 1

    return {
        "n_labeled": n_labeled,
        "n_rows": n_rows,
        "n_in_S_conj": n_in_S_conj,
        "n_in_S_rig": n_in_S_rig,
        "n_violations_conj": n_violations_conj,
        "n_violations_rig": n_violations_rig,
        "n_tight_conj": n_tight_conj,
        "n_tight_rig": n_tight_rig,
        "n_bound_gt1_conj": n_bound_gt1_conj,
        "n_bound_gt1_rig": n_bound_gt1_rig,
        "per_group": dict(per_group_conj),
        "per_group_in_S": dict(per_group_in_S_conj),
        "per_group_violations": dict(per_group_violations),
        "per_group_tight": dict(per_group_tight),
        "violation_examples": violation_examples,
    }


def print_corpus_summary(stats: dict) -> None:
    print("\n=== Corpus sweep ===\n")
    n = stats["n_rows"]
    print(f"labeled rows           : {n}")
    print(f"rows in S (conjectural): {stats['n_in_S_conj']}")
    print(f"rows in S (rigorous)   : {stats['n_in_S_rig']}")
    print(f"violations (conj)      : {stats['n_violations_conj']}")
    print(f"violations (rig)       : {stats['n_violations_rig']}")
    print(f"tight (conj)           : {stats['n_tight_conj']}")
    print(f"tight (rig)            : {stats['n_tight_rig']}")
    if stats["n_in_S_conj"] > 0:
        rate = stats["n_tight_conj"] / stats["n_in_S_conj"]
        print(f"tightness rate (conj)  : {rate:.3f}")
    if stats["n_in_S_rig"] > 0:
        rate = stats["n_tight_rig"] / stats["n_in_S_rig"]
        print(f"tightness rate (rig)   : {rate:.3f}")

    print("\nPer-group:")
    for grp in sorted(stats["per_group"].keys()):
        total = stats["per_group"][grp]
        in_S = stats["per_group_in_S"].get(grp, 0)
        viol = stats["per_group_violations"].get(grp, 0)
        tight = stats["per_group_tight"].get(grp, 0)
        print(
            f"  {grp:<10} rows={total:>5} in_S={in_S:>5} viol={viol:>3} tight={tight:>3}"
        )

    if stats["violation_examples"]:
        print("\nFirst few violations:")
        for v in stats["violation_examples"][:10]:
            print(
                f"  iid={v['instance_id']} "
                f"[[{v['n']},{v['k']},{v['d_exact']}]] "
                f"bound={v['lower_conj']} "
                f"A={v['A_poly']!r} B={v['B_poly']!r}"
            )


# ---------------------------------------------------------------------------
# Markdown writer
# ---------------------------------------------------------------------------


def write_markdown(bravyi_rows: list[dict], stats: dict) -> Path:
    out_path = LAB_ROOT / "notes" / "T2R5.3_eval.md"
    lines: list[str] = []
    lines.append("# T2R5.3 — Homological bound: Bravyi + corpus evaluation")
    lines.append("")
    lines.append(
        "Bound implemented: **Symons–Rajput–Browne 2025 cover-graph "
        "chain-map distance transfer** ([arXiv:2511.13560](https://arxiv.org/abs/2511.13560))."
    )
    lines.append(
        "Distance lookups use the Bravyi table + the labeled corpus DB."
    )
    lines.append("")
    lines.append("## 1. Bravyi-table evaluation")
    lines.append("")
    lines.append(
        "| code_id | n | k | d | S (conj) | lower (conj) | upper (conj) | "
        "S (rig) | lower (rig) | best usable base |"
    )
    lines.append(
        "| --- | --: | --: | --: | :---: | --: | --: | :---: | --: | --- |"
    )
    for r in bravyi_rows:
        lines.append(
            f"| {r['code_id']} | {r['n']} | {r['k']} | {r['d_exact']} | "
            f"{'yes' if r['S_conj'] else 'no'} | {r['lower_conj']} | "
            f"{r['upper_conj']} | "
            f"{'yes' if r['S_rig'] else 'no'} | {r['lower_rig']} | "
            f"{r['best_base']} |"
        )
    lines.append("")
    lines.append(
        "Columns: `S (conj)` = does the SRB conjectural condition hold "
        "(any-h cover with known base distance > 1); `S (rig)` = same with "
        "h restricted to odd values (SRB Theorem 4.6 / 4.7 rigorous regime); "
        "`lower (conj/rig)` = `bb_homological_bound`; `upper (conj)` = "
        "`bb_homological_upper_bound`; `best usable base` = the strongest "
        "base used by the conjectural bound."
    )
    lines.append("")
    lines.append("## 2. Corpus sweep")
    lines.append("")
    lines.append(
        f"* labeled corpus rows (`d_exact IS NOT NULL`): **{stats['n_rows']}**"
    )
    lines.append(
        f"* rows where S (conjectural) holds: **{stats['n_in_S_conj']}** "
        f"({100 * stats['n_in_S_conj'] / max(stats['n_rows'], 1):.1f}%)"
    )
    lines.append(
        f"* rows where S (rigorous) holds: **{stats['n_in_S_rig']}** "
        f"({100 * stats['n_in_S_rig'] / max(stats['n_rows'], 1):.1f}%)"
    )
    lines.append(
        f"* **violations of `bound ≤ d_exact` (conj)**: "
        f"**{stats['n_violations_conj']}** "
        f"of {stats['n_in_S_conj']} in-S rows"
    )
    lines.append(
        f"* violations (rig): **{stats['n_violations_rig']}** "
        f"of {stats['n_in_S_rig']} in-S rows"
    )
    lines.append(
        f"* tight (conj, `bound = d_exact`): **{stats['n_tight_conj']}**"
    )
    lines.append(
        f"* tight (rig): **{stats['n_tight_rig']}**"
    )
    if stats["n_in_S_conj"] > 0:
        rate = stats["n_tight_conj"] / stats["n_in_S_conj"]
        lines.append(
            f"* tightness rate (conj): **{rate:.3f}** "
            f"({stats['n_tight_conj']}/{stats['n_in_S_conj']})"
        )
    if stats["n_in_S_rig"] > 0:
        rate = stats["n_tight_rig"] / stats["n_in_S_rig"]
        lines.append(
            f"* tightness rate (rig): **{rate:.3f}** "
            f"({stats['n_tight_rig']}/{stats['n_in_S_rig']})"
        )
    lines.append("")
    lines.append("### Per-group breakdown")
    lines.append("")
    lines.append(
        "| group_struct | rows | in_S (conj) | violations | tight |"
    )
    lines.append(
        "| --- | --: | --: | --: | --: |"
    )
    for grp in sorted(stats["per_group"].keys()):
        total = stats["per_group"][grp]
        in_S = stats["per_group_in_S"].get(grp, 0)
        viol = stats["per_group_violations"].get(grp, 0)
        tight = stats["per_group_tight"].get(grp, 0)
        lines.append(f"| {grp} | {total} | {in_S} | {viol} | {tight} |")
    lines.append("")
    if stats["violation_examples"]:
        lines.append("### First few violations")
        lines.append("")
        for v in stats["violation_examples"][:10]:
            lines.append(
                f"* iid={v['instance_id']} "
                f"[[{v['n']},{v['k']},{v['d_exact']}]] "
                f"bound={v['lower_conj']} "
                f"A={v['A_poly']!r} B={v['B_poly']!r} "
                f"group={v['group_struct']}"
            )
        lines.append("")
    else:
        lines.append("### Violations")
        lines.append("")
        lines.append("**Zero violations.** The SRB §7 conjecture is "
                     "consistent with all corpus rows where it fires.")
        lines.append("")
    lines.append("## 3. Interpretation")
    lines.append("")
    lines.append(
        "* If the **conjectural** corpus violations = 0, the SRB §7 "
        "conjecture survives the lab's largest empirical test to date "
        "(complementing the paper's own Tables 1–10)."
    )
    lines.append(
        "* If **rigorous** corpus violations = 0, that's also consistent — "
        "the rigorous form is a published theorem, only the empirical "
        "corroboration is new."
    )
    lines.append(
        "* The headline question is whether the bound is **tight on gross**. "
        "It is **not**: gross is a double cover (h=2) of [[72,12,6]] with "
        "d_base=6, so `bb_homological_bound(gross) = 6 < d_gross = 12`. "
        "This is the §6k obstruction articulated in T2R5.0_literature.md: "
        "the cover index for gross is even, so the chain-map argument "
        "loses a factor of 2 in lower-bound strength."
    )
    out_path.write_text("\n".join(lines) + "\n")
    return out_path


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    print("Loading base-distance lookup (Bravyi table + corpus)…")
    lookup = _CorpusBackedLookup()

    print("\nEvaluating Bravyi instances…")
    bravyi_rows = evaluate_bravyi_table(lookup)
    print_bravyi_table(bravyi_rows)

    print("\nSweeping corpus (may take a few minutes for ~4k rows)…")
    stats = sweep_corpus(lookup)
    print_corpus_summary(stats)

    print("\nWriting markdown report…")
    out_path = write_markdown(bravyi_rows, stats)
    print(f"\nWrote {out_path.relative_to(LAB_ROOT.parent.parent)}")


if __name__ == "__main__":
    main()

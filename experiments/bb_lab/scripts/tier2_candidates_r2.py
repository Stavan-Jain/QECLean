"""Tier-2 Round 2 candidate distance bound proposals.

Round 1's headline conjecture (Jacobson-radical sum) was falsified
at 10.5% on the corpus and on bb_72_12_6 directly. The diagnosis
(per `pipeline/attempts/bb_distance_conjecture/result.md`): the RHS
was a *dimension invariant* (`Σ |O| · μ_O = dim ker M_A`), which
governs `k` per Bravyi 2024 Lemma 1, not `d`.

This round (R2) restricts the candidate space to RHS values that are
**weight invariants** — quantities defined via the minimum non-zero
Hamming weight of code-defined subspaces. See
`notes/T2R2.1_weight_invariants_inventory.md` for the rule and
inventory.

Each candidate below carries:
- formula
- citation (or explicit "new-to-us" tag)
- rationale: why the RHS is a weight invariant
- expected direction (lower/upper bound)
- known caveat

Run via:

    uv run python scripts/tier2_candidates_r2.py

Output is a tightness/violation report per candidate.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

# Local imports — package layout has `src/bb_lab/` on path via uv sync.
from bb_lab.corpus import Corpus
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.weight_invariants import (
    _intersection_subgroup_order,
    _support_subgroup_order,
    bch_per_orbit_lower_bound,
    joint_per_orbit_dual_distance,
    max_per_orbit_dual_distance,
    min_per_orbit_dual_distance,
    per_orbit_dual_distance,
    tz_lower_bound,
)

# Reuse evaluation harness
sys.path.insert(0, str(Path(__file__).resolve().parent))
from tier2_explore import (  # noqa: E402  (path-aware import)
    Candidate,
    evaluate_candidate,
    render_report,
)


# ===========================================================================
# Helpers: row -> (G, A, B)
# ===========================================================================


def _row_polys(r: dict) -> tuple[ZmZn, Poly, Poly]:
    """Reconstruct (G, A, B) from a corpus row."""
    G = ZmZn(int(r["ell"]), int(r["m"]))
    A = Poly.from_string(r["A_poly"], G)
    B = Poly.from_string(r["B_poly"], G)
    return G, A, B


# ===========================================================================
# Candidate 1: TZ_lower_recomputed (BASELINE — already in lit candidates)
# ===========================================================================
#
# d_X ≥ ⌈min(d_A^⊥, d_B^⊥) / c⌉  where c = |G_a ∩ G_b|
#
# Weight invariant check: numerator is min of two weight invariants
# (classical dual minimum distances). Denominator is a structural
# subgroup order. The ratio's value depends on the numerator's
# weight content, so this is a weight invariant.
#
# This is Lin-Pryadko 2023 Statement 12 (LP23 §IV.F) and equivalent to
# Kovalev-Pryadko 2013 Theorem 5. **Already in the literature.**

def _tz_lower_cached(r):
    """TZ lower bound, using cached corpus values when available."""
    G, A, B = _row_polys(r)
    if r.get("min_wt_ker_A") is not None and r.get("min_wt_ker_B") is not None:
        d_A = int(r["min_wt_ker_A"])
        d_B = int(r["min_wt_ker_B"])
        c = _intersection_subgroup_order(A.support, B.support, G)
        return max(1, math.ceil(min(d_A, d_B) / max(c, 1)))
    return tz_lower_bound(A, B, G)


TZ_lower = Candidate(
    name="r2_TZ_lower_recomputed",
    formula="d ≥ ⌈min(d_A^⊥, d_B^⊥) / c⌉",
    citation=(
        "Lin-Pryadko 2023 arXiv:2306.16400 Statement 12 (§IV.F); equivalent "
        "to Kovalev-Pryadko 2013 arXiv:1212.6703 Theorem 5. Recomputed here "
        "as a callable feature (not just a Candidate lambda)."
    ),
    requires=("A_poly", "B_poly", "ell", "m", "min_wt_ker_A", "min_wt_ker_B"),
    bound_fn=_tz_lower_cached,
)


# ===========================================================================
# Candidate 2: tanner_girth_lower_bound
# ===========================================================================
#
# d ≥ ⌈(girth + 2) / 4⌉  for regular Tanner graphs (Sipser-Spielman
# LDPC distance bound). For BB codes with row weight w = 6 and
# variable degree d_v = 3, this is the standard LDPC bound. It's
# almost always loose on BB codes (since BB codes have engineered
# distance >> girth-bound), but it MUST hold rigorously. A violation
# would be a bug or counterexample to the bound's hypotheses.
#
# Citation: Sipser-Spielman 1996 "Expander codes" Theorem 19 (a
# similar form); Roffe et al. 2020 qLDPC review §3.
#
# Weight invariant: tanner_girth is the length of the shortest cycle
# in the Tanner graph, a combinatorial (and graph-theoretic) min over
# weighted paths.

tanner_girth_lower = Candidate(
    name="r2_tanner_girth_lower",
    formula="d ≥ ⌈(tanner_girth + 2) / 4⌉  (Sipser-Spielman shape)",
    citation=(
        "Sipser-Spielman 1996; specifically the 'expansion implies "
        "distance' theorem family. For Tanner graphs with girth g, "
        "iterative-decoding distance ≥ (g+2)/4 under expansion. The "
        "LDPC literature gives this as a baseline; almost always loose "
        "on engineered BB codes."
    ),
    requires=("tanner_girth",),
    bound_fn=lambda r: max(
        1, math.ceil((int(r["tanner_girth"]) + 2) / 4)
    ) if r["tanner_girth"] != float("inf") else 1,
)


# ===========================================================================
# Candidate 3: bch_per_axis_lower
# ===========================================================================
#
# d ≥ min(bch_per_axis(A), bch_per_axis(B))
#
# BCH/cyclotomic-coset per-axis dual distance lower bound. For each
# axis of G = Z_ℓ × Z_m, the polynomial A's projection to that axis
# gives a univariate cyclic code; BCH bound on its dual distance.
# `bch_per_orbit_lower_bound` aggregates max over axes (a valid lower
# bound on d_A^⊥).
#
# Then d_X ≤ min(d_A^⊥, d_B^⊥) implies (textbook upper bound), so this
# candidate gives an INDIRECT bound: `d_X ≥ ?` ... wait, this needs
# the OPPOSITE direction. BCH bounds d_A^⊥ FROM BELOW, so it
# strengthens the TZ lower bound through a LOWER-bound numerator.
#
# Specifically: bch_per_orbit_lower_bound(A) ≤ d_A^⊥ = min_wt_ker_A.
# So d_X ≥ ⌈min(bch_axis(A), bch_axis(B)) / c⌉ would be WEAKER than
# TZ_lower (smaller numerator → smaller bound).
#
# **However**, the BCH bound IS computable from the polynomial WITHOUT
# the full kernel enumeration. So for large-G instances where
# `min_wt_ker_A` is infeasible (`dim_ker > 22`), BCH is the fallback.
#
# Citation: Bose-Chaudhuri-Hocquenghem 1960 (canonical BCH bound).
# Multivariate generalization implicit; per-axis projection is
# textbook for product cyclic codes.
#
# Weight invariant: bch_per_orbit_lower_bound's value depends on the
# cyclotomic-coset structure of the support, which is a weight
# invariant of the per-axis dual code.

bch_lower = Candidate(
    name="r2_bch_per_axis_lower",
    formula="d ≥ ⌈min(BCH(A), BCH(B)) / c⌉  (per-axis BCH lb on d_A^⊥, divided by c)",
    citation=(
        "Bose-Chaudhuri-Hocquenghem 1960; per-axis projection bound is "
        "textbook for product cyclic codes. Strictly WEAKER than "
        "TZ_lower (since BCH(A) ≤ d_A^⊥), but corpus-computable "
        "without kernel enumeration. Useful as a sanity check and "
        "fallback for large kernels."
    ),
    requires=("A_poly", "B_poly", "ell", "m"),
    bound_fn=lambda r: (
        lambda G, A, B: max(
            1,
            math.ceil(
                min(
                    bch_per_orbit_lower_bound(A, G),
                    bch_per_orbit_lower_bound(B, G),
                ) / max(
                    _intersection_subgroup_order(A.support, B.support, G), 1,
                )
            ),
        )
    )(*_row_polys(r)),
)


# ===========================================================================
# Candidate 4: tz_or_girth_composite (a defensible STRONGER lower bound)
# ===========================================================================
#
# d ≥ max(TZ_lower, tanner_girth_lower)
#
# Both ingredients are valid lower bounds. The max is therefore also
# a valid lower bound and is at least as tight as either alone.
# Citation: composition of LP23 Stmt 12 + Sipser-Spielman expander
# bound. NOT NEW in mathematics, but NEW packaging.

def _tz_or_girth_composite(r):
    G, A, B = _row_polys(r)
    # Use cached min_wt_ker if available; else compute (may fail for
    # large kernels).
    try:
        if r.get("min_wt_ker_A") is not None and r.get("min_wt_ker_B") is not None:
            d_A = int(r["min_wt_ker_A"])
            d_B = int(r["min_wt_ker_B"])
            c = _intersection_subgroup_order(A.support, B.support, G)
            tz = max(1, math.ceil(min(d_A, d_B) / max(c, 1)))
        else:
            tz = tz_lower_bound(A, B, G)
    except Exception:
        tz = 1
    girth = r.get("tanner_girth")
    if girth is None or girth == float("inf"):
        girth_lb = 1
    else:
        girth_lb = max(1, math.ceil((int(girth) + 2) / 4))
    return max(tz, girth_lb)


tz_or_girth_lower = Candidate(
    name="r2_tz_or_girth_composite",
    formula="d ≥ max(TZ_lower, ⌈(girth+2)/4⌉)  (composite of two lit lbs)",
    citation=(
        "Composite of Lin-Pryadko Stmt 12 + Sipser-Spielman expander "
        "bound. Both ingredients are individually valid lower bounds "
        "(in the literature); the max is therefore valid. Not "
        "introducing new mathematical content."
    ),
    requires=("A_poly", "B_poly", "ell", "m", "tanner_girth"),
    bound_fn=_tz_or_girth_composite,
)


# ===========================================================================
# Candidate 5: tz_with_joint_per_orbit_numerator (NEW, refinement attempt)
# ===========================================================================
#
# d ≥ ⌈min_{O ∈ V_A ∩ V_B} d_O^⊥_joint(A, B) / c⌉
#
# Where d_O^⊥_joint(A, B) is the minimum Hamming weight of any
# nonzero vector in `(ker M_A ∩ ker M_B)_O` — the joint kernel
# restricted to orbit O's isotypical component.
#
# Rationale: an X-logical's restriction to orbit O is constrained by
# the joint per-orbit kernel structure. The minimum over orbits gives
# a lower bound on the contribution of any orbit-component to the
# weight, and dividing by c captures the standard TZ "stabilizer
# averaging" loss.
#
# Caveat: this is heuristically motivated, not a rigorous derivation.
# Corpus testing will tell whether it holds.
#
# Weight invariant: joint_per_orbit_dual_distance is per-orbit min
# Hamming weight, a weight invariant of the joint isotypical kernel.
# Divided by structural c.

def _tz_joint_per_orbit_min(r):
    G, A, B = _row_polys(r)
    # Only compute when the joint kernel is small enough.
    # Bail out if dim_ker too big — we'd time out.
    if int(r.get("dim_ker_A", 99)) > 18 or int(r.get("dim_ker_B", 99)) > 18:
        return 1  # vacuous
    jpods = joint_per_orbit_dual_distance(A, B, G, max_kernel_dim=18)
    if not jpods:
        # No joint vanishing orbits — bound is vacuous (use 1)
        return 1
    min_d_O = min(jpods.values())
    c = _intersection_subgroup_order(A.support, B.support, G)
    return max(1, math.ceil(min_d_O / max(c, 1)))


tz_joint_per_orbit_lower = Candidate(
    name="r2_tz_joint_per_orbit_lower",
    formula="d ≥ ⌈min_O d_O^⊥_joint(A, B) / c⌉  (joint per-orbit numerator)",
    citation=(
        "NEW-TO-US. Refinement of LP23 Stmt 12 using joint per-orbit "
        "kernel min weights instead of global d_A^⊥, d_B^⊥. "
        "Heuristically motivated; corpus testing determines validity. "
        "Joint per-orbit dual distance is a weight invariant of the "
        "isotypical joint kernel; the structural denominator c is the "
        "intersection subgroup order. Both ingredients have weight "
        "content (the numerator) and structural content (the "
        "denominator), in the LP23 spirit but per-orbit."
    ),
    requires=("A_poly", "B_poly", "ell", "m", "dim_ker_A", "dim_ker_B"),
    bound_fn=_tz_joint_per_orbit_min,
)


# ===========================================================================
# Candidate 6: tz_lower_with_classical_dual_check (a SANITY candidate)
# ===========================================================================
#
# `tz_lower_with_safety = min(TZ_lower, min_wt_ker_A, min_wt_ker_B)`.
# This caps the TZ lower bound by the textbook upper bound. Since
# TZ_lower ≤ d_A^⊥ structurally (because c ≥ 1 and TZ_lower divides
# d_A^⊥ by c), the cap is usually inactive. Included as a safety net
# in case TZ_lower has a numerical bug pushing it above the textbook
# bound — that would indicate a buggy candidate.

tz_safe_lower = Candidate(
    name="r2_tz_safe_lower",
    formula="d ≥ min(TZ_lower, d_A^⊥, d_B^⊥)  (TZ capped by textbook bound)",
    citation=(
        "Safety cap on TZ_lower to ensure no spurious violations from "
        "the lambda's ceiling/floor edge cases. TZ_lower ≤ d_A^⊥ "
        "always when c ≥ 1; this cap is vacuous in practice."
    ),
    requires=("A_poly", "B_poly", "ell", "m", "min_wt_ker_A", "min_wt_ker_B"),
    bound_fn=lambda r: min(
        _tz_lower_cached(r),
        int(r["min_wt_ker_A"]),
        int(r["min_wt_ker_B"]),
    ),
)


# ===========================================================================
# Candidate 7: support_indicator_lower
# ===========================================================================
#
# d ≥ ⌈(d_A^⊥) / |V_A ∩ V_B|⌉  where |V_A ∩ V_B| is the count of
# orbits where both A and B vanish. (Reusing min_wt_ker_A as the
# per-orbit-numerator-equivalent under TZ logic.)
#
# This is a NOVEL form: structural denominator is the count of joint
# vanishing orbits, not the intersection subgroup order.
#
# Weight-invariance: numerator is min_wt_ker_A (weight invariant);
# denominator is a structural count. Output value depends on the
# weight content via the numerator. WEIGHT INVARIANT.
#
# Caveat: this is heuristic — the structural reasoning that should
# underlie it is "different joint orbits give independent constraints
# on logicals", but that's not a proof. Test on corpus.

def _support_indicator_lower(r):
    """⌈d_A^⊥ / |V_A ∩ V_B|⌉ where |V_A ∩ V_B| is the number of joint
    vanishing orbits on G_odd. Uses min_wt_ker_A from corpus."""
    from bb_lab.algebraic_features import (
        g_odd_frobenius_orbits,
        jacobson_radical_depth,
    )
    G, A, B = _row_polys(r)
    orbits = g_odd_frobenius_orbits(G)
    n_joint = sum(
        1 for o in orbits
        if jacobson_radical_depth(A, o, G) > 0
        and jacobson_radical_depth(B, o, G) > 0
    )
    n_joint = max(n_joint, 1)
    return max(1, math.ceil(int(r["min_wt_ker_A"]) / n_joint))


support_indicator_lower = Candidate(
    name="r2_support_indicator_lower",
    formula="d ≥ ⌈min_wt_ker_A / |V_A ∩ V_B|⌉  (joint-orbit-count denominator)",
    citation=(
        "NEW-TO-US. Replaces TZ's c = |G_a ∩ G_b| with a per-orbit "
        "count: the number of orbits where both A and B vanish. "
        "Heuristically: each joint vanishing orbit is a source of "
        "potential logical operator support, and the d_A^⊥ / |V_A∩V_B| "
        "ratio approximates 'each orbit contributes at least 1/|V_A∩V_B| "
        "of the dual code's minimum weight'. Corpus testing required."
    ),
    requires=("A_poly", "B_poly", "ell", "m", "min_wt_ker_A"),
    bound_fn=_support_indicator_lower,
)


# ===========================================================================
# Aggregate
# ===========================================================================

R2_CANDIDATES: tuple[Candidate, ...] = (
    TZ_lower,
    tanner_girth_lower,
    bch_lower,
    tz_or_girth_lower,   # NEW (composite of two valid lbs)
    tz_joint_per_orbit_lower,  # NEW (expected to fail)
    tz_safe_lower,
    support_indicator_lower,  # NEW (expected to fail)
)


# ===========================================================================
# Direction-aware evaluation: lower bound checks
# ===========================================================================
#
# `evaluate_candidate` reports `bound - d_exact` as "looseness" and
# treats negative values as violations (assuming UPPER bound). For a
# LOWER bound, we need the OPPOSITE convention: violation if
# `bound > d_exact`.
#
# We add a thin wrapper that re-interprets the looseness/violation
# semantics. The candidate fn returns the LOWER bound; we flag rows
# where `bound > d_exact` (the candidate predicts d ≥ bound, but
# d_exact says otherwise — violation).


def evaluate_lower_bound(corpus, cand, group_filter=None):
    """Evaluate a candidate as a LOWER bound. Violations: bound > d_exact.

    Returns a report dict with semantics:
    - `tight`: bound == d_exact (predicts exactly the right distance)
    - `loose`: bound < d_exact (true lb, but loose)
    - `violation`: bound > d_exact (FALSIFIES the candidate)
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
                f"corpus is missing required column(s) {missing}"
            ),
        }
    base = corpus.filter(d_exact_is_not_null=True)
    if group_filter:
        base = base.filter(group_struct_in=list(group_filter))
    for col in cand.requires:
        base = base.filter(**{f"{col}_is_not_null": True})

    n_apl = 0
    n_tight = 0
    n_violations = 0
    looseness_vals: list[int] = []
    violations: list[dict] = []
    tight_examples: list[dict] = []
    loose_examples: list[dict] = []
    per_group_tight: dict[str, int] = {}
    per_group_total: dict[str, int] = {}
    per_group_violations: dict[str, int] = {}

    for r in base:
        try:
            bound = int(cand.bound_fn(r))
        except Exception as e:
            violations.append({"row": r["instance_id"], "error": str(e)})
            continue
        d = int(r["d_exact"])
        diff = d - bound  # positive: bound is loose (d > bound)
        n_apl += 1
        looseness_vals.append(diff)
        g = r["group_struct"]
        per_group_total[g] = per_group_total.get(g, 0) + 1
        if bound > d:
            # VIOLATION: candidate predicts d ≥ bound but d_exact < bound
            n_violations += 1
            per_group_violations[g] = per_group_violations.get(g, 0) + 1
            if len(violations) < 5:
                violations.append({
                    "row": r["instance_id"], "d_exact": d,
                    "bound": bound, "group": g, "n": r["n"], "k": r["k"],
                    "A_poly": r["A_poly"], "B_poly": r["B_poly"],
                })
        elif bound == d:
            n_tight += 1
            per_group_tight[g] = per_group_tight.get(g, 0) + 1
            if len(tight_examples) < 3:
                tight_examples.append({
                    "id": r["instance_id"], "group": g,
                    "n": r["n"], "k": r["k"], "d": d, "bound": bound,
                })
        else:
            if len(loose_examples) < 3:
                loose_examples.append({
                    "id": r["instance_id"], "group": g,
                    "n": r["n"], "k": r["k"], "d": d, "bound": bound,
                    "looseness": diff,
                })

    return {
        "name": cand.name,
        "formula": cand.formula,
        "citation": cand.citation,
        "applicable_rows": n_apl,
        "tight_count": n_tight,
        "tight_rate": n_tight / max(n_apl, 1),
        "violations_count": n_violations,
        "violation_rate": n_violations / max(n_apl, 1),
        "violations": violations,
        "mean_looseness": (
            sum(looseness_vals) / len(looseness_vals)
            if looseness_vals else None
        ),
        "max_looseness": max(looseness_vals) if looseness_vals else None,
        "min_looseness": min(looseness_vals) if looseness_vals else None,
        "per_group_tight": {
            g: (per_group_tight.get(g, 0), per_group_total[g])
            for g in per_group_total
        },
        "per_group_violations": dict(per_group_violations),
        "tight_examples": tight_examples,
        "loose_examples": loose_examples,
    }


def render_lower_bound_report(reports: list[dict]) -> str:
    out: list[str] = []
    for r in reports:
        out.append(f"\n=== {r['name']} ===")
        out.append(f"  formula:  {r['formula']}")
        out.append(f"  citation: {r['citation'][:120]}...")
        if "note" in r:
            out.append(f"  note: {r['note']}")
            continue
        out.append(f"  applicable rows: {r['applicable_rows']}")
        out.append(
            f"  tight (bound == d): {r['tight_count']} "
            f"({r['tight_rate']*100:.1f}%)"
        )
        out.append(
            f"  violations (bound > d): {r['violations_count']} "
            f"({r['violation_rate']*100:.1f}%)"
        )
        if r["violations_count"] > 0:
            out.append("  VIOLATION EXAMPLES:")
            for v in r["violations"][:3]:
                if "error" in v:
                    out.append(f"    {v['row'][:8]} ERROR: {v['error']}")
                else:
                    out.append(
                        f"    {v['row'][:8]}  {v['group']:8s}  "
                        f"d_exact={v['d_exact']}  bound={v['bound']}  "
                        f"(violates by +{v['bound']-v['d_exact']}) "
                        f"A={v['A_poly']}, B={v['B_poly']}"
                    )
        out.append(
            f"  looseness (d - bound):  min={r['min_looseness']}  "
            f"mean={r['mean_looseness']:.2f}  max={r['max_looseness']}"
            if r["mean_looseness"] is not None else "  looseness: n/a"
        )
        if r["per_group_violations"]:
            out.append("  per group violations:")
            for g in sorted(r["per_group_violations"]):
                out.append(
                    f"    {g:10s}  {r['per_group_violations'][g]} violations"
                )
        if r["tight_examples"]:
            out.append("  tight examples:")
            for e in r["tight_examples"]:
                out.append(
                    f"    {e['id'][:8]}  {e['group']:10s}  "
                    f"n={e['n']}  k={e['k']}  d={e['d']}  bound={e['bound']}"
                )
    return "\n".join(out)


# ===========================================================================
# Main
# ===========================================================================


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Tier-2 Round 2 candidate distance lower bounds. Read-only."
    )
    ap.add_argument(
        "--db", type=Path, default=None,
        help="Path to bb_instances.duckdb (default: lab's)."
    )
    ap.add_argument(
        "--groups", nargs="*", default=None,
        help="Restrict to these group_struct labels."
    )
    ap.add_argument(
        "--limit", type=int, default=None,
        help="Limit corpus rows (for smoke testing)."
    )
    args = ap.parse_args()

    corpus = Corpus(db_path=args.db) if args.db else Corpus()
    summary = corpus.summary()
    print(f"corpus: {summary}")

    if args.limit is not None:
        corpus = corpus.limited(int(args.limit))

    reports = [
        evaluate_lower_bound(corpus, c, args.groups) for c in R2_CANDIDATES
    ]
    print(render_lower_bound_report(reports))


if __name__ == "__main__":
    main()

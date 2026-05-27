"""Adversarial Attack 2: weight-5 BB codes over Z_6 × Z_6, c ≥ 3.

The R1 (odd-weight) hypothesis was added to exclude 78 weight-4 violators
on Z_6 × Z_6. Weight-3 codes are extensively tested (the corpus). Weight-5
codes (also odd ✓ R1) have NEVER been tested.

If the odd-weight hypothesis is doing "real work" (some augmentation-ideal
mechanism), weight-5 should also satisfy. If it's anti-fit to weight-4
violators specifically, weight-5 may produce new violators.

Strategy:
  - Enumerate weight-5 canonical BB pairs over Z_6 × Z_6 (k >= 1)
  - Filter to in-hypothesis: c >= 3 (G_odd = Z_3 × Z_3 is automatic; elem-ab)
  - For each in-scope case, compute R4 bound and SAT distance (max_d <= 8)
  - Stop after ~30 minutes wall-clock or 30 in-scope cases tested
  - Report any violator

A single violation falsifies the conjecture.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from tier3_cv3_r4_crossorbit import r4_cross_orbit_bound
from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.degeneracy import is_g_odd_elementary_abelian
from bb_lab.enumerate_bb import enumerate_canonical_pairs
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    joint_support_subgroup_index,
)
from bb_lab.sat_distance import x_distance


WALL_BUDGET_SECONDS = 1800   # 30 minutes
MAX_IN_SCOPE_CASES = 50
MAX_SAT_WEIGHT = 8           # cap SAT search to keep runtime sane


def supports_to_poly_string(support, G):
    """Convert a list of group-element tuples to a polynomial string."""
    parts = []
    for g in support:
        if isinstance(g, tuple):
            a, b = g
        else:
            a, b = g
        terms = []
        if a > 0:
            terms.append("x" if a == 1 else f"x^{a}")
        if b > 0:
            terms.append("y" if b == 1 else f"y^{b}")
        if not terms:
            parts.append("1")
        else:
            parts.append("*".join(terms))
    return " + ".join(parts)


def main():
    print("=== Adversarial Attack 2: weight-5 BB codes over Z_6 × Z_6 ===\n", flush=True)
    G = ZmZn(6, 6)
    print(f"  G = {G.label()},  G_odd = Z_3 × Z_3,  G_2 = Z_2 × Z_2")
    print(f"  G_odd elem-ab: {is_g_odd_elementary_abelian(G)}")
    print(f"  Weight = 5 (odd; R1 hypothesis satisfied trivially)")
    print(f"  Filter: c >= 3 (in-hypothesis)")
    print(f"  Budget: {WALL_BUDGET_SECONDS}s wall-clock, {MAX_IN_SCOPE_CASES} in-scope cases\n")
    print("  Enumerating canonical pairs (k >= 1)...\n", flush=True)

    t_start = time.time()
    n_canonical = 0
    n_inscope = 0
    n_tested = 0
    n_violations = 0
    n_tight = 0
    n_loose = 0
    n_sat_failed = 0
    n_r4_unable = 0

    violators: list[dict] = []

    for inst in enumerate_canonical_pairs(G, weight=5, only_k_geq=1, verbose=False):
        n_canonical += 1
        elapsed = time.time() - t_start
        if elapsed > WALL_BUDGET_SECONDS:
            print(f"\n  (wall-clock budget {WALL_BUDGET_SECONDS}s reached)", flush=True)
            break
        if n_inscope >= MAX_IN_SCOPE_CASES:
            print(f"\n  (max in-scope cases {MAX_IN_SCOPE_CASES} reached)", flush=True)
            break

        # Materialize A, B as Polys
        A_str = supports_to_poly_string(inst.canonical.A_support, G)
        B_str = supports_to_poly_string(inst.canonical.B_support, G)
        A = Poly.from_string(A_str, G)
        B = Poly.from_string(B_str, G)
        c = joint_support_subgroup_index(A, B, G)
        if c < 3:
            continue
        n_inscope += 1

        # Compute R4 bound
        bound_r4, info = r4_cross_orbit_bound(A, B, G)
        bound_orig = bb_radical_bound(A, B, G)
        if bound_r4 is None:
            n_r4_unable += 1
            print(
                f"  [{n_inscope:>2d}] (canon #{n_canonical}, t={elapsed:6.1f}s)  "
                f"A={A_str!r}  B={B_str!r}  k={inst.k}  c={c}  "
                f"R4 UNABLE (basis dim too large)",
                flush=True,
            )
            continue

        # Compute exact distance via SAT (cap at MAX_SAT_WEIGHT)
        checks = bb_check_matrices(A, B)
        try:
            res = x_distance(checks, weight_upper_bound=MAX_SAT_WEIGHT)
            d = res.distance
        except Exception as exc:
            d = None
            n_sat_failed += 1
            print(f"      SAT failed: {exc}", flush=True)
            continue

        n_tested += 1
        if d is None:
            n_sat_failed += 1
            continue
        if bound_r4 > d:
            n_violations += 1
            violators.append({
                "A": A_str, "B": B_str, "c": c, "k": inst.k,
                "bound_orig": bound_orig, "bound_r4": bound_r4, "d": d,
                "info": info,
            })
            verdict = f"*** VIOLATION (R4 {bound_r4} > d {d}) ***"
        elif bound_r4 == d:
            n_tight += 1
            verdict = f"tight (= {d})"
        else:
            n_loose += 1
            verdict = f"loose ({bound_r4} < d={d}, gap {d - bound_r4})"

        print(
            f"  [{n_inscope:>2d}] (canon #{n_canonical}, t={elapsed:6.1f}s)  "
            f"A={A_str:<22}  B={B_str:<22}  k={inst.k}  c={c}  "
            f"orig={bound_orig}  R4={bound_r4}  d={d}  {verdict}",
            flush=True,
        )

    elapsed_total = time.time() - t_start
    print(f"\n=== Summary ===")
    print(f"  Canonical pairs scanned: {n_canonical}")
    print(f"  In-scope (c >= 3):       {n_inscope}")
    print(f"  Successfully tested:     {n_tested}")
    print(f"  Tight:                   {n_tight}")
    print(f"  Loose-correct:           {n_loose}")
    print(f"  **Violations:**          {n_violations}")
    print(f"  SAT failures:            {n_sat_failed}")
    print(f"  R4 unable (dim>22):      {n_r4_unable}")
    print(f"  Wall-clock:              {elapsed_total:.1f}s")
    if n_violations > 0:
        print(f"\n  *** CONJECTURE FALSIFIED ***")
        for v in violators:
            print(f"    A={v['A']!r}, B={v['B']!r}, c={v['c']}, R4={v['bound_r4']}, d={v['d']}")
    elif n_tested == 0:
        print(f"\n  Inconclusive (no test completed).")
    else:
        print(f"\n  Conjecture SURVIVES this attack on weight-5 Z_6×Z_6 c>=3 ({n_tested} tested, 0 violations).")


if __name__ == "__main__":
    main()

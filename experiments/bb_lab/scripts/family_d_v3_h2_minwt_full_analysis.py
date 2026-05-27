"""Family D v3 — full corpus analysis of min_wt(H_2) formulas.

Building on the session-1 observation, this script tests a hierarchy of
candidate formulas for min_wt(H_2) on the SAT-verified corpus:

  Formula 1 (FOUR-NINTHS, Bravyi family):  min_wt = (4/9)·|G|
  Formula 2 (TWO-THIRDS, "single homomorphism phi: G -> Z_3"):  min_wt = (2/3)·|G|
  Formula 3 (LOWER, via 2-torsion):  min_wt = (1/2)·|G|, (1/3)·|G|, (1/4)·|G|, etc.

The categorization:

  - Bravyi-family pattern: holds when both axes' Z_3 projections give
    multiset {0,1,2} on supp(A) and supp(B). Element factors as f(x)*g(y).

  - Single-Z_3-homomorphism: holds when there exists phi: G -> Z_3 with
    phi(supp(A)) = phi(supp(B)) = {0,1,2}. Element is 1_{G \\ ker phi}.

  - Lower (when |G| has higher 2-torsion or other structure): when the
    "diagonal subgroup" element is further decomposable.

This script classifies each corpus row and validates the formula.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

import duckdb
import numpy as np

from bb_lab.checks import circulant
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly


TARGET = Counter({0: 1, 1: 1, 2: 1})


def axis_projection_image(poly: Poly, axis: int) -> Counter:
    """Z_3-image of support projected to a single axis (mod 3)."""
    return Counter(g[axis] % 3 for g in poly.support)


def joint_z3_homomorphism_works(A: Poly, B: Poly, ell: int, m: int) -> tuple[int, int]:
    """Return (a, b) ∈ Z_3 × Z_3 \\ {(0,0)} such that phi(x,y) = a*x + b*y mod 3
    sends both supp(A) and supp(B) to multiset {0, 1, 2}. Returns (-1, -1)
    if none exists."""
    for a in range(3):
        for b in range(3):
            if a == 0 and b == 0:
                continue
            phi_A = Counter((a * g[0] + b * g[1]) % 3 for g in A.support)
            phi_B = Counter((a * g[0] + b * g[1]) % 3 for g in B.support)
            if phi_A == TARGET and phi_B == TARGET:
                return (a, b)
    return (-1, -1)


def axis_factorable(A: Poly, B: Poly) -> bool:
    """Returns True if both A and B have phi_x(supp) = phi_y(supp) = {0,1,2}.

    This is the "Bravyi family" condition where tensor-product solutions exist.
    """
    sx_A = axis_projection_image(A, 0)
    sx_B = axis_projection_image(B, 0)
    sy_A = axis_projection_image(A, 1)
    sy_B = axis_projection_image(B, 1)
    return sx_A == TARGET and sx_B == TARGET and sy_A == TARGET and sy_B == TARGET


def supports_span(A: Poly, B: Poly) -> tuple[bool, bool]:
    """Returns (has_x_dependence, has_y_dependence) — True if some monomial
    in A or B has nonzero exponent in x (resp. y).
    """
    has_x = any(g[0] != 0 for g in A.support | B.support)
    has_y = any(g[1] != 0 for g in A.support | B.support)
    return has_x, has_y


def min_wt_H_2(M_A: np.ndarray, M_B: np.ndarray) -> tuple[int, int]:
    basis = nullspace_f2(np.concatenate([M_A, M_B], axis=0))
    dim = basis.shape[0]
    if dim == 0:
        return 0, 0
    n = basis.shape[1]
    best = n + 1
    if dim <= 16:
        for mask in range(1, 1 << dim):
            v = np.zeros(n, dtype=np.uint8)
            for i in range(dim):
                if (mask >> i) & 1:
                    v ^= basis[i]
            w = int(v.sum())
            if 0 < w < best:
                best = w
        return dim, best
    from itertools import combinations
    for size in range(1, 17):
        for subset in combinations(range(dim), size):
            v = np.zeros(n, dtype=np.uint8)
            for i in subset:
                v ^= basis[i]
            w = int(v.sum())
            if 0 < w < best:
                best = w
    return dim, best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=500)
    parser.add_argument("--all-aligned", action="store_true")
    parser.add_argument("--all", action="store_true",
                        help="ALL SAT-verified rows (not just aligned)")
    args = parser.parse_args()

    repo = Path(__file__).resolve().parents[1]
    db_path = repo / "data" / "bb_instances.duckdb"
    con = duckdb.connect(str(db_path), read_only=True)

    if args.all:
        q = """SELECT instance_id, ell, m, A_poly, B_poly, d_exact
               FROM bb_instances
               WHERE d_exact IS NOT NULL
               ORDER BY ell*m, instance_id"""
    else:
        # Aligned (3 | both factors)
        q = """SELECT instance_id, ell, m, A_poly, B_poly, d_exact
               FROM bb_instances
               WHERE d_exact IS NOT NULL
                 AND (ell % 3 = 0) AND (m % 3 = 0)
               ORDER BY ell*m, instance_id"""
    rows = con.execute(q).fetchall()
    if not args.all_aligned and not args.all:
        # Stratified sample
        by_group = defaultdict(list)
        for r in rows:
            by_group[(r[1], r[2])].append(r)
        per_group = max(1, args.limit // max(1, len(by_group)))
        rows = []
        for grp_rows in by_group.values():
            rows.extend(grp_rows[:per_group])
        rows = rows[:args.limit]

    print(f"Processing {len(rows)} rows.\n")

    classify = defaultdict(list)
    by_group_cat = defaultdict(lambda: defaultdict(list))
    formula_match: dict[str, int] = {
        "match_4/9": 0,
        "match_2/3": 0,
        "match_other": 0,
    }
    formula_total: dict[str, int] = {
        "category_axis_factorable": 0,
        "category_z3_hom_only": 0,
        "category_z3_subgroup_fails": 0,
        "category_one_axis_degenerate": 0,
    }
    for row in rows:
        inst_id, ell, m, A_str, B_str, d_exact = row
        G = ZmZn(ell, m)
        A = Poly.from_string(A_str, G)
        B = Poly.from_string(B_str, G)
        M_A = circulant(A)
        M_B = circulant(B)
        dim_h2, min_wt = min_wt_H_2(M_A, M_B)
        n = G.cardinality

        # Classification
        has_x, has_y = supports_span(A, B)
        # In a "weight-3 BB code", we'd expect both axes to contribute.
        # Degenerate if only one axis.
        if not has_x or not has_y:
            cat = "category_one_axis_degenerate"
        elif axis_factorable(A, B):
            cat = "category_axis_factorable"
        else:
            a, b = joint_z3_homomorphism_works(A, B, ell, m)
            if (a, b) != (-1, -1):
                cat = "category_z3_hom_only"
            else:
                cat = "category_z3_subgroup_fails"

        formula_total[cat] += 1

        # Predicted formula
        if cat == "category_axis_factorable":
            predicted = (4 * n) / 9
        elif cat == "category_z3_hom_only":
            predicted = (2 * n) / 3
        else:
            predicted = None

        if predicted is not None and abs(min_wt - predicted) < 1e-9:
            if cat == "category_axis_factorable":
                formula_match["match_4/9"] += 1
            elif cat == "category_z3_hom_only":
                formula_match["match_2/3"] += 1
        else:
            formula_match["match_other"] += 1

        classify[cat].append({
            'inst_id': inst_id, 'ell': ell, 'm': m, 'n': n,
            'A': A_str, 'B': B_str,
            'dim_h2': dim_h2, 'min_wt': min_wt,
            'predicted': predicted,
            'ratio_to_4_9': min_wt / ((4 * n) / 9) if n else 0,
            'ratio_to_2_3': min_wt / ((2 * n) / 3) if n else 0,
        })
        by_group_cat[(ell, m)][cat].append(min_wt)

    print(f"=== Classification ===")
    for cat in ['category_axis_factorable', 'category_z3_hom_only', 'category_z3_subgroup_fails', 'category_one_axis_degenerate']:
        n_in_cat = formula_total[cat]
        if cat == "category_axis_factorable":
            matches = formula_match["match_4/9"]
            label = f"(predicted (4/9)|G|)"
        elif cat == "category_z3_hom_only":
            matches = formula_match["match_2/3"]
            label = f"(predicted (2/3)|G|)"
        else:
            matches = 0
            label = "(no clean formula)"
        print(f"  {cat}: {n_in_cat} instances {label}")
        if n_in_cat > 0 and matches > 0:
            print(f"    matched formula: {matches}/{n_in_cat} = {matches/n_in_cat*100:.1f}%")

    print(f"\n=== Match rates within categories ===")
    print(f"  (4/9) formula in axis-factorable category: {formula_match['match_4/9']}/{formula_total['category_axis_factorable']}")
    print(f"  (2/3) formula in z3-hom-only category: {formula_match['match_2/3']}/{formula_total['category_z3_hom_only']}")

    # Show mismatches in axis-factorable category
    if formula_total['category_axis_factorable'] > 0:
        print(f"\n=== Mismatches in axis-factorable category ===")
        for r in classify['category_axis_factorable']:
            if abs(r['min_wt'] - r['predicted']) > 1e-9:
                print(f"  {r['inst_id'][:16]}: Z_{r['ell']}xZ_{r['m']} A={r['A']}, B={r['B']}")
                print(f"    min_wt = {r['min_wt']}, predicted (4/9)|G| = {r['predicted']}, ratio = {r['ratio_to_4_9']:.4f}")

    # Z3-hom-only mismatches
    print(f"\n=== Mismatches in z3-hom-only category (first 10) ===")
    cnt = 0
    for r in classify['category_z3_hom_only']:
        if abs(r['min_wt'] - r['predicted']) > 1e-9:
            print(f"  {r['inst_id'][:16]}: Z_{r['ell']}xZ_{r['m']} A={r['A']}, B={r['B']}")
            print(f"    min_wt = {r['min_wt']}, predicted (2/3)|G| = {r['predicted']}, ratio = {r['ratio_to_2_3']:.4f}")
            cnt += 1
            if cnt >= 10:
                break

    # By group breakdown
    print(f"\n=== Match by group structure ===")
    for grp in sorted(by_group_cat):
        ell, m = grp
        n = ell * m
        for cat in sorted(by_group_cat[grp]):
            cat_mins = by_group_cat[grp][cat]
            unique_mins = sorted(set(cat_mins))
            print(f"  Z_{ell}xZ_{m} ({cat}): {len(cat_mins)} cases, "
                  f"min_wts in {unique_mins[:6]}{'...' if len(unique_mins) > 6 else ''}")


if __name__ == "__main__":
    main()

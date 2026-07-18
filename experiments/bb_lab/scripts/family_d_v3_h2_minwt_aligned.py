"""Family D v3 — pin down the (4/9)|G| pattern in min_wt(H_2), aligned groups.

Refined hypothesis: For BB codes with G = Z_ℓ × Z_m where 3 | gcd(ℓ, m),
the relation min_wt(H_2(Koszul(A,B))) = (4/9)·|G| holds *for separable*
(x-y-decomposable) polynomials A, B.

Separable: every monomial in A is either purely x^i or purely y^j (no
mixed x*y terms). The 5 Bravyi instances are all separable.

Non-separable BB codes (with x*y monomials) probably follow a DIFFERENT
formula or no clean formula.

This script:
  1. Restricts to "aligned" groups (3 | gcd(ℓ, m)).
  2. Separately reports separable vs. non-separable instances.
  3. Tests the (4/9)|G| equality on both subsets.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

import argparse
import duckdb
import numpy as np

from bb_lab.checks import circulant
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly


def is_separable(p: Poly) -> bool:
    """A poly is separable if every monomial is purely x^i or purely y^j."""
    for g in p.support:
        x_part, y_part = g[0], g[1]
        if x_part != 0 and y_part != 0:
            return False
    return True


def min_wt_H_2(M_A: np.ndarray, M_B: np.ndarray) -> tuple[int, int]:
    stacked = np.concatenate([M_A, M_B], axis=0)
    basis = nullspace_f2(stacked)
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
    parser.add_argument("--all", action="store_true",
                        help="Probe all aligned-group SAT-verified rows.")
    parser.add_argument("--limit", type=int, default=300)
    args = parser.parse_args()

    repo = Path(__file__).resolve().parents[1]
    db_path = repo / "data" / "bb_instances.duckdb"
    con = duckdb.connect(str(db_path), read_only=True)

    # Aligned: 3 | gcd(ell, m). Pre-filter by ell % 3 = 0 AND m % 3 = 0.
    q = """
        SELECT instance_id, code_id, ell, m, n, k, A_poly, B_poly, d_exact
        FROM bb_instances
        WHERE d_exact IS NOT NULL
          AND (ell % 3 = 0) AND (m % 3 = 0)
        ORDER BY n, instance_id
    """
    if not args.all:
        q += f" LIMIT {args.limit}"
    rows = con.execute(q).fetchall()
    print(f"Processing {len(rows)} aligned (3 | gcd(ℓ,m)) SAT-verified rows.\n")

    # Separate by separability.
    separable_results = []
    nonseparable_results = []
    matches_separable = 0
    matches_nonseparable = 0

    by_group_separable: dict[tuple[int, int], list[tuple[bool, int, int]]] = defaultdict(list)
    by_group_nonsep: dict[tuple[int, int], list[tuple[bool, int, int]]] = defaultdict(list)

    n_processed = 0
    for row in rows:
        instance_id, code_id, ell, m, n_qubits, k, A_str, B_str, d_exact = row
        G = ZmZn(ell, m)
        A = Poly.from_string(A_str, G)
        B = Poly.from_string(B_str, G)
        sep = is_separable(A) and is_separable(B)

        M_A = circulant(A)
        M_B = circulant(B)
        dim_h2, min_wt = min_wt_H_2(M_A, M_B)
        expected = (4 * G.cardinality) / 9
        matches = (min_wt > 0) and (abs(min_wt - expected) < 1e-9)

        rec = (matches, min_wt, dim_h2)
        if sep:
            separable_results.append((instance_id, ell, m, dim_h2, min_wt, expected, matches, A_str, B_str))
            if matches:
                matches_separable += 1
            by_group_separable[(ell, m)].append(rec)
        else:
            nonseparable_results.append((instance_id, ell, m, dim_h2, min_wt, expected, matches, A_str, B_str))
            if matches:
                matches_nonseparable += 1
            by_group_nonsep[(ell, m)].append(rec)

        n_processed += 1
        if n_processed % 50 == 0:
            print(f"  ... {n_processed} processed.", flush=True)

    print(f"\nProcessed {n_processed} aligned rows.")
    print(f"  Separable: {len(separable_results)} ({matches_separable} match)")
    print(f"  Non-separable: {len(nonseparable_results)} ({matches_nonseparable} match)")
    print()

    print("Match rate by group (SEPARABLE):")
    for grp in sorted(by_group_separable):
        recs = by_group_separable[grp]
        m_cnt = sum(1 for r in recs if r[0])
        # Distribution of min_wts
        wts = [r[1] for r in recs]
        unique_wts = sorted(set(wts))
        print(f"  Z_{grp[0]}xZ_{grp[1]}: {m_cnt}/{len(recs)} match. "
              f"min_wts: {sorted(set(wts))[:8]}{'...' if len(unique_wts) > 8 else ''}")

    print("\nMatch rate by group (NON-SEPARABLE):")
    for grp in sorted(by_group_nonsep):
        recs = by_group_nonsep[grp]
        m_cnt = sum(1 for r in recs if r[0])
        wts = [r[1] for r in recs]
        unique_wts = sorted(set(wts))
        print(f"  Z_{grp[0]}xZ_{grp[1]}: {m_cnt}/{len(recs)} match. "
              f"min_wts: {sorted(set(wts))[:8]}{'...' if len(unique_wts) > 8 else ''}")

    # Detail any separable mismatches
    print("\nSeparable mismatches (first 10):")
    cnt_sep_mis = 0
    for rec in separable_results:
        if not rec[6]:
            print(f"  {rec[0]} (Z_{rec[1]}xZ_{rec[2]}, |G|={rec[1]*rec[2]})")
            print(f"    A = {rec[7]}, B = {rec[8]}")
            print(f"    dim_H_2 = {rec[3]}, min_wt = {rec[4]}, (4/9)|G| = {rec[5]:.2f}")
            cnt_sep_mis += 1
            if cnt_sep_mis >= 10:
                break

    # Histogram of (min_wt / (4/9|G|)) ratios for separable
    print("\nSeparable: distribution of min_wt / ((4/9)|G|) ratios:")
    from collections import Counter
    ratios_sep = Counter()
    for rec in separable_results:
        if rec[5] > 0:
            ratio = rec[4] / rec[5]
            ratios_sep[round(ratio, 4)] += 1
    for r in sorted(ratios_sep):
        print(f"  ratio {r}: {ratios_sep[r]} rows")

    print("\nNon-separable: distribution of min_wt / ((4/9)|G|) ratios:")
    ratios_ns = Counter()
    for rec in nonseparable_results:
        if rec[5] > 0:
            ratio = rec[4] / rec[5]
            ratios_ns[round(ratio, 4)] += 1
    for r in sorted(ratios_ns):
        print(f"  ratio {r}: {ratios_ns[r]} rows")


if __name__ == "__main__":
    main()

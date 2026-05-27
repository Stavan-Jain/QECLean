"""Family C v1 — spectral-radius empirical predictor check.

For a BB code with polynomial A on G = Z_ell × Z_m, the Cayley-graph
adjacency M_A has eigenvalues at each character χ of G, given by
  λ_A(χ) = sum_{(a, b) ∈ supp(A)} χ((a, b))
        = sum_{(a, b) ∈ supp(A)} ω_ell^{k1·a} · ω_m^{k2·b}
with χ = χ_{k1, k2}. The non-trivial spectral radius is
  λ_2(A) := max_{(k1, k2) ≠ (0, 0)} |λ_A(χ_{k1, k2})|.

The CLASSICAL Tanner spectral bound on ker(M_A) is
  d_classical ≥ n · (w - λ_2) / (2w)   with w = |supp(A)|.
But d_classical(H_X) ≤ row weight of H_X = 6 (any single row is in the
kernel modulo something), so it does NOT directly lower-bound the
quantum d_X. We instead use λ_2 as an EMPIRICAL FEATURE and check
correlation with d_X across the SAT-verified corpus.

Question: is there a clean function f(λ_2_A, λ_2_B) that predicts
tight/loose-by-k buckets of d_X?
"""

from __future__ import annotations

import cmath
import math
from collections import Counter
from pathlib import Path

import duckdb

from bb_lab.group import ZmZn
from bb_lab.poly import Poly

DB_PATH = Path(__file__).resolve().parent.parent / "data" / "bb_instances.duckdb"


def cayley_spectral_radius_nontrivial(
    supp: frozenset, ell: int, m: int
) -> float:
    """Max over non-trivial characters χ of |sum_{g ∈ supp} χ(g)|."""
    max_abs = 0.0
    for k1 in range(ell):
        for k2 in range(m):
            if k1 == 0 and k2 == 0:
                continue
            s = 0j
            for (a, b) in supp:
                s += cmath.exp(2j * cmath.pi * (k1 * a / ell + k2 * b / m))
            max_abs = max(max_abs, abs(s))
    return max_abs


def main() -> None:
    con = duckdb.connect(str(DB_PATH), read_only=True)
    rows = con.execute(
        """SELECT instance_id, group_struct, ell, m, A_poly, B_poly,
                  n, k, d_exact, A_weight, B_weight
             FROM bb_instances
            WHERE d_exact IS NOT NULL
              AND k >= 2
              AND A_weight = 3 AND B_weight = 3
            ORDER BY group_struct, n, k"""
    ).fetchall()
    print(f"Examining {len(rows)} weight-3 SAT-verified rows")
    print()

    # For each row: compute (λ_2_A, λ_2_B, gap, d). Bucket by group_struct
    # to see if the relationship varies.
    by_group_gap = {}  # group_struct → list of (gap, d)
    for iid, gs, ell, m_, A_str, B_str, n, k, d, wa, wb in rows:
        G = ZmZn(ell, m_)
        A = Poly.from_string(A_str, G)
        B = Poly.from_string(B_str, G)
        lam_A = cayley_spectral_radius_nontrivial(A.support, ell, m_)
        lam_B = cayley_spectral_radius_nontrivial(B.support, ell, m_)
        # "Spectral gap" = weight - max non-trivial eigenvalue.
        # Tighter gap (closer to weight=3) means worse expansion.
        gap_A = wa - lam_A
        gap_B = wb - lam_B
        gap_min = min(gap_A, gap_B)
        by_group_gap.setdefault(gs, []).append((gap_min, d))

    # Aggregate stats per group, plus across-corpus correlation.
    print(f"{'group':10s} {'rows':>5s}  {'gap range':18s}  {'d range':12s}  {'correlation':>12s}")
    all_gaps, all_ds = [], []
    for gs in sorted(by_group_gap):
        data = by_group_gap[gs]
        gaps = [g for g, d in data]
        ds = [d for g, d in data]
        # Simple Pearson via numpy substitute.
        n_pts = len(data)
        if n_pts < 2:
            corr_str = "n/a"
        else:
            mg = sum(gaps) / n_pts
            md = sum(ds) / n_pts
            num = sum((g - mg) * (d - md) for g, d in data)
            denA = math.sqrt(sum((g - mg) ** 2 for g in gaps))
            denB = math.sqrt(sum((d - md) ** 2 for d in ds))
            if denA == 0 or denB == 0:
                corr_str = "n/a"
            else:
                corr = num / (denA * denB)
                corr_str = f"{corr:+.3f}"
        print(
            f"{gs:10s}  {n_pts:>4d}  "
            f"[{min(gaps):.2f}, {max(gaps):.2f}]    "
            f"[{min(ds):>2d}, {max(ds):>2d}]    "
            f"{corr_str:>12s}"
        )
        all_gaps += gaps
        all_ds += ds

    # Across-corpus correlation.
    n_all = len(all_gaps)
    if n_all >= 2:
        mg = sum(all_gaps) / n_all
        md = sum(all_ds) / n_all
        num = sum((g - mg) * (d - md) for g, d in zip(all_gaps, all_ds))
        denA = math.sqrt(sum((g - mg) ** 2 for g in all_gaps))
        denB = math.sqrt(sum((d - md) ** 2 for d in all_ds))
        corr = num / (denA * denB) if denA and denB else 0.0
        print()
        print(f"Across {n_all} rows: Pearson correlation(gap, d) = {corr:+.3f}")

    # Quick sanity: gross-class rows specifically.
    print()
    print("Z12xZ6 rows (gross's group):")
    for gap, d in sorted(by_group_gap.get("Z12xZ6", [])):
        print(f"  gap={gap:.3f}  d={d}")


if __name__ == "__main__":
    main()

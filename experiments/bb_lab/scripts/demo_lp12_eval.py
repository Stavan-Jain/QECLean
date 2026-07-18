"""Demo: end-to-end Tier-2/3 evaluation of Lin–Pryadko Statement 12.

Computes `bound(row) = ⌈min(d_A^⊥, d_B^⊥) / c⌉` over every corpus row
where the required features are present, compares to d_exact (and d_ub
where d_exact is missing), aggregates tightness/violation stats, and
breaks down by Bravyi instances + per-group.

Read-only against the corpus DB so it can run while a fill-distances
write is in flight.

Usage:
  cd experiments/bb_lab
  uv run python scripts/demo_lp12_eval.py
"""

from __future__ import annotations

import math
from collections import Counter
from pathlib import Path

import duckdb

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.weight_invariants import tz_lower_bound, _intersection_subgroup_order

DB_PATH = Path(__file__).resolve().parent.parent / "data" / "bb_instances.duckdb"


def lp12_bound(min_wt_ker_A: int, min_wt_ker_B: int, c: int) -> int:
    """LP Statement 12: d ≥ ⌈min(d_A^⊥, d_B^⊥) / c⌉.

    Here c = |G_a ∩ G_b| (ORDER of intersection), per Lin-Pryadko's
    paper and bb_lab/weight_invariants.tz_lower_bound — NOT the index
    [G_a : G_a ∩ G_b] returned by radical_weight.joint_support_subgroup_index.
    """
    return max(1, math.ceil(min(min_wt_ker_A, min_wt_ker_B) / max(c, 1)))


def main() -> None:
    con = duckdb.connect(str(DB_PATH), read_only=True)
    rows = con.execute(
        """SELECT instance_id, code_id, group_struct, ell, m, A_poly, B_poly,
                  n, k, d_exact, d_ub, min_wt_ker_A, min_wt_ker_B
             FROM bb_instances
            WHERE min_wt_ker_A IS NOT NULL AND min_wt_ker_B IS NOT NULL
              AND d_exact IS NOT NULL
              AND k >= 2
            ORDER BY group_struct, n, k"""
    ).fetchall()

    applicable = 0
    violations = 0
    tight = 0
    looseness: list[int] = []
    per_group = Counter()
    per_group_tight = Counter()
    bravyi: list[tuple[str, int, int, int | None]] = []

    BRAVYI_CODE_IDS = {
        "bb_72_12_6": ("[[72,12,6]]", 6),
        "bb_90_8_10": ("[[90,8,10]]", 10),
        "bb_108_8_10": ("[[108,8,10]]", 10),
        "gross": ("[[144,12,12]] gross", 12),
        "bb_288_12_18": ("[[288,12,18]]", 18),
    }

    for row in rows:
        (iid, code_id, gs, ell, m_, A_str, B_str, n, k,
         d_exact, d_ub, mwa, mwb) = row
        if mwa is None or mwb is None:
            continue
        d_known = d_exact if d_exact is not None else d_ub
        if d_known is None:
            continue
        # Parse polys and compute c = |G_a ∩ G_b| on the fly.
        try:
            G = ZmZn(ell, m_)
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
            c = _intersection_subgroup_order(A.support, B.support, G)
        except Exception:
            continue
        bound = lp12_bound(mwa, mwb, c)
        gap = d_known - bound  # > 0 = loose; < 0 = violation; 0 = tight
        applicable += 1
        per_group[gs] += 1
        if gap < 0:
            violations += 1
            print(f"  VIOLATION {code_id}: bound={bound}, d={d_known}")
        elif gap == 0:
            tight += 1
            per_group_tight[gs] += 1
        looseness.append(gap)

        if code_id in BRAVYI_CODE_IDS:
            display, _ = BRAVYI_CODE_IDS[code_id]
            bravyi.append((display, bound, d_known, d_exact))

    print(f"\n===== LP Statement 12 demo eval =====")
    print(f"Applicable rows:       {applicable}")
    print(f"Violations:            {violations}")
    print(f"Tight (gap = 0):       {tight}  ({100*tight/applicable:.2f}%)")
    print(f"Mean looseness:        {sum(looseness)/len(looseness):.2f}")
    print(f"Max looseness:         {max(looseness)}")
    print(f"Min looseness:         {min(looseness)}")
    print()
    print("Tightness by group (top 12):")
    for gs, total in sorted(per_group.items(), key=lambda x: -x[1])[:12]:
        t = per_group_tight[gs]
        pct = 100 * t / total
        print(f"  {gs:12s}  tight={t:5d}/{total:5d}  ({pct:5.1f}%)")
    print()
    print("Bravyi-table instances:")
    for display, bound, d_known, d_exact in bravyi:
        method = "d_exact" if d_exact is not None else "d_ub"
        gap = d_known - bound
        print(f"  {display:25s}  bound={bound:2d}, {method}={d_known:3d}, "
              f"{'TIGHT' if gap == 0 else f'loose by {gap}'}")


if __name__ == "__main__":
    main()

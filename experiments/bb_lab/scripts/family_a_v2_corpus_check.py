"""Family A v2 — Step 3: corpus check on the y'-spread observation.

The H_UNIT² note observed (on 4 cases): spread ≥ 3 → tight, spread ≤ 2 →
potentially-loose. Extending the test to all SAT-verified corpus rows
in groups with non-trivial G_2 (where the y'-direction exists).

For each row:
  * find joint-vanishing orbits (where both A and B vanish in F_2[G_odd])
  * for each such orbit, compute spread_A(O) and spread_B(O)
  * compute C-v3 bound via bb_radical_bound; gap = d_exact - bound

Output: dump per-row + aggregate. If spread predicts tightness, we'll
see a clean split: high-min-spread → gap == 0, low-min-spread → gap < 0
(violation of C-v3) or gap > 0 (loose but valid).
"""

from __future__ import annotations

from collections import Counter
from pathlib import Path

import duckdb

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_depth,
)
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import bb_radical_bound

# Import our v2 function
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from family_a_v2_seed_check import a_O_y_spread

DB_PATH = Path(__file__).resolve().parent.parent / "data" / "bb_instances.duckdb"

# Groups with 2 | |G| (non-trivial G_2) where the y'-direction is defined.
TARGET_GROUPS = ("Z6xZ6", "Z9xZ6", "Z12xZ6", "Z3xZ6", "Z4xZ6", "Z5xZ6")


def find_joint_vanishing_reps(A: Poly, B: Poly, G: ZmZn):
    """Yield (orbit_rep, orbit_size) for each joint-vanishing orbit."""
    orbits = g_odd_frobenius_orbits(G)
    for orbit in orbits:
        if jacobson_radical_depth(A, orbit, G) == 0:
            continue
        if jacobson_radical_depth(B, orbit, G) == 0:
            continue
        rep = next(iter(orbit))
        yield rep, len(orbit)


def main() -> None:
    con = duckdb.connect(str(DB_PATH), read_only=True)
    rows = con.execute(
        f"""SELECT instance_id, group_struct, ell, m, A_poly, B_poly, n, k, d_exact
              FROM bb_instances
             WHERE d_exact IS NOT NULL
               AND group_struct IN {TARGET_GROUPS}
               AND k >= 2
             ORDER BY group_struct, n, k"""
    ).fetchall()
    print(f"Examining {len(rows)} SAT-verified rows in non-trivial-G_2 groups")
    print()

    # For each row, compute: min spread across joint-vanishing orbits,
    # C-v3 bound, gap = d - bound.
    by_spread: dict[int, Counter] = {}  # min_spread → Counter of (gap, count)
    rows_examined = 0
    rows_skipped_no_jv = 0
    examples: dict[int, list] = {}  # min_spread → list of (group, d, bound, gap)
    for iid, gs, ell, m_, A_str, B_str, n, k, d in rows:
        try:
            G = ZmZn(ell, m_)
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
        except Exception:
            continue
        jv = list(find_joint_vanishing_reps(A, B, G))
        if not jv:
            rows_skipped_no_jv += 1
            continue
        spreads_A = [a_O_y_spread(A, G, rep) for rep, _sz in jv]
        spreads_B = [a_O_y_spread(B, G, rep) for rep, _sz in jv]
        min_spread = min(min(spreads_A), min(spreads_B))
        bound = bb_radical_bound(A, B, G)
        if bound == 0 or bound == float("inf"):
            continue
        gap = d - bound  # >0 loose, =0 tight, <0 violation of bound
        by_spread.setdefault(min_spread, Counter())[gap] += 1
        examples.setdefault(min_spread, []).append((gs, d, int(bound), gap))
        rows_examined += 1

    print(f"  rows examined:        {rows_examined}")
    print(f"  rows skipped (no JV): {rows_skipped_no_jv}")
    print()
    print(f"  By min_spread (over joint-vanishing orbits):")
    print(f"  {'spread':>6s} {'rows':>6s}  {'gap distribution':50s}")
    for sp in sorted(by_spread):
        ctr = by_spread[sp]
        total = sum(ctr.values())
        tight = ctr.get(0, 0)
        violations = sum(c for g, c in ctr.items() if g < 0)
        loose = total - tight - violations
        gap_summary = (
            f"tight={tight:4d}, loose={loose:4d}, VIOLATION={violations:4d}  "
            f"({100*tight/total:5.1f}% tight)"
        )
        print(f"  {sp:>6d} {total:>6d}  {gap_summary}")
    print()
    # Spot examples for each spread bucket
    print(f"  Spot examples (spread → sample rows):")
    for sp in sorted(examples):
        sample = examples[sp][:4]
        print(f"  spread={sp}: " + ", ".join(f"{gs} d={d} b={b} gap={g:+d}" for gs, d, b, g in sample))


if __name__ == "__main__":
    main()

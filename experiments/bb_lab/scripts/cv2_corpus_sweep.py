"""C-v2 corpus sweep — test bb_radical_bound conjectures vs d_exact.

Reads `data/bb_instances.duckdb` read-only (HANDOFF_C2 §7). For every
labeled row, computes each formulation's bound and reports violations,
tightness, looseness.

Single corpus violation falsifies the corresponding conjecture (HANDOFF_C2
§C-v2.3).

Run with:
    uv run python scripts/cv2_corpus_sweep.py
"""

from __future__ import annotations

import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field

from bb_lab.algebraic_features import g_odd_frobenius_orbits
from bb_lab.corpus import Corpus
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    bb_radical_bound_alt,
    joint_support_subgroup_index,
)

FORMULATIONS = ["primary", "any-orbit", "multi-mu", "geometric"]
# "sum" is excluded — known to violate on gross by §5 Alt-C, kept in
# the impl for completeness but not corpus-tested here.


def parse_group(s: str) -> tuple[int, int]:
    parts = s.split("x")
    return int(parts[0][1:]), int(parts[1][1:])


@dataclass
class Stats:
    tested: int = 0
    vacuous: int = 0
    tight: int = 0
    violations: list[dict] = field(default_factory=list)
    loose_total: int = 0
    sum_gap: int = 0
    gap_hist: Counter = field(default_factory=Counter)


def sweep() -> dict[str, Stats]:
    rows = Corpus().filter(d_exact_is_not_null=True)
    t0 = time.time()
    stats: dict[str, Stats] = {f: Stats() for f in FORMULATIONS}
    total_rows = 0
    for row in rows:
        total_rows += 1
        d_actual = int(row["d_exact"])
        try:
            ell, m = parse_group(row["group_struct"])
            G = ZmZn(ell, m)
            A = Poly.from_string(row["A_poly"], G)
            B = Poly.from_string(row["B_poly"], G)
        except Exception as e:
            print(f"  parse-skip {row['instance_id'][:8]}: {e}")
            continue

        for f in FORMULATIONS:
            try:
                if f == "primary":
                    bound = bb_radical_bound(A, B, G)
                else:
                    bound = bb_radical_bound_alt(A, B, G, formulation=f)
            except Exception as e:
                print(
                    f"  compute-error {row['instance_id'][:8]} {f}: {e}"
                )
                continue

            s = stats[f]
            s.tested += 1
            if bound == 0:
                s.vacuous += 1
                continue
            if bound > d_actual:
                s.violations.append({
                    "instance_id": row["instance_id"],
                    "group_struct": row["group_struct"],
                    "n": row["n"],
                    "d_actual": d_actual,
                    "bound": bound,
                    "A_poly": row["A_poly"],
                    "B_poly": row["B_poly"],
                    "c": joint_support_subgroup_index(A, B, G),
                })
            elif bound == d_actual:
                s.tight += 1
                s.gap_hist[0] += 1
            else:
                s.loose_total += 1
                gap = d_actual - bound
                s.sum_gap += gap
                s.gap_hist[gap] += 1

        if total_rows % 200 == 0:
            print(
                f"  ... {total_rows} rows ({time.time() - t0:.1f}s elapsed)"
            )

    print(f"\nTotal labeled rows: {total_rows}, time {time.time() - t0:.1f}s")
    return stats


def report(stats: dict[str, Stats]) -> None:
    for f, s in stats.items():
        non_vac = s.tested - s.vacuous
        print(f"\n=== {f} ===")
        print(f"  tested:           {s.tested}")
        print(f"  vacuous (no orb): {s.vacuous}")
        print(f"  violations:       {len(s.violations)}")
        print(f"  tight (bound==d): {s.tight}")
        print(f"  loose (bound<d):  {s.loose_total}")
        if non_vac > 0:
            tight_pct = 100.0 * s.tight / non_vac
            print(f"  tightness rate:   {tight_pct:.1f}% of non-vacuous")
            mean_gap = s.sum_gap / non_vac if non_vac > 0 else 0
            print(f"  mean gap:         {mean_gap:.2f}")
        if s.violations:
            # First few violation samples
            print(f"  sample violations (first 5):")
            for v in s.violations[:5]:
                print(
                    f"    {v['instance_id'][:8]} {v['group_struct']}: "
                    f"d={v['d_actual']}, bound={v['bound']}, c={v['c']}, "
                    f"A={v['A_poly']!r}, B={v['B_poly']!r}"
                )
            # Group violations by group_struct
            by_group: defaultdict[str, int] = defaultdict(int)
            for v in s.violations:
                by_group[v["group_struct"]] += 1
            print(f"  violations by group: {dict(by_group)}")
            # Group violations by c
            by_c: defaultdict[int, int] = defaultdict(int)
            for v in s.violations:
                by_c[v["c"]] += 1
            print(f"  violations by c: {dict(sorted(by_c.items()))}")


def main() -> None:
    stats = sweep()
    report(stats)


if __name__ == "__main__":
    main()

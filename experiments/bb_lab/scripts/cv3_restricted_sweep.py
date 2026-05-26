"""C-v3 restricted corpus sweep — narrowed conjecture on
elementary-abelian-G_odd rows.

Reads the corpus read-only, filters to rows where
`is_g_odd_elementary_abelian(G)` is True, and tests the
C-v2 `bb_radical_bound` conjecture. Per HANDOFF_C3 §2:

    If G_odd is elementary abelian (loose def: each prime-part is
    elementary abelian), then
        d_X(BB(G, A, B)) ≥ (1/c) · min_O min(w_1(A, O), w_1(B, O))

Cross-stratifies by:
  * loose-def: each prime-part elementary abelian (includes bb_90).
  * strict-def: G_odd ≅ (Z_p)^k for one prime p (excludes bb_90).
  * c value: the LP joint-support index.

Run:
    uv run python scripts/cv3_restricted_sweep.py
"""

from __future__ import annotations

import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field

from bb_lab.corpus import Corpus
from bb_lab.degeneracy import (
    g_odd_decomposition,
    g_odd_elementary_prime,
    is_g_odd_elementary_abelian,
)
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    joint_support_subgroup_index,
)


def parse_group(s: str) -> tuple[int, int]:
    parts = s.split("x")
    return int(parts[0][1:]), int(parts[1][1:])


@dataclass
class Bucket:
    total: int = 0
    tight: int = 0
    loose: int = 0
    violations: list[dict] = field(default_factory=list)
    vacuous: int = 0


def sweep() -> dict:
    rows = Corpus().filter(d_exact_is_not_null=True)
    by_loose: dict[bool, Bucket] = defaultdict(Bucket)
    by_strict: dict[str, Bucket] = defaultdict(Bucket)
    by_loose_and_c: dict[tuple[bool, int], Bucket] = defaultdict(Bucket)
    by_strict_and_c: dict[tuple[str, int], Bucket] = defaultdict(Bucket)
    by_group_loose: dict[str, Bucket] = defaultdict(Bucket)
    by_decomp: dict[tuple[int, ...], Bucket] = defaultdict(Bucket)

    t0 = time.time()
    total = 0
    for row in rows:
        total += 1
        try:
            ell, m = parse_group(row["group_struct"])
            G = ZmZn(ell, m)
            A = Poly.from_string(row["A_poly"], G)
            B = Poly.from_string(row["B_poly"], G)
        except Exception as e:
            continue
        loose = is_g_odd_elementary_abelian(G)
        prime = g_odd_elementary_prime(G)
        strict_label = (
            f"single-prime-{prime}" if prime is not None
            else ("loose-not-strict" if loose else "not-loose")
        )
        c = joint_support_subgroup_index(A, B, G)
        try:
            bound = bb_radical_bound(A, B, G)
        except Exception:
            continue
        d = int(row["d_exact"])
        decomp = g_odd_decomposition(G)

        def update(bucket: Bucket):
            bucket.total += 1
            if bound == 0:
                bucket.vacuous += 1
            elif bound > d:
                bucket.violations.append({
                    "instance_id": row["instance_id"],
                    "group_struct": row["group_struct"],
                    "decomp": decomp,
                    "n": row["n"],
                    "d": d,
                    "bound": bound,
                    "c": c,
                    "A_poly": row["A_poly"],
                    "B_poly": row["B_poly"],
                })
            elif bound == d:
                bucket.tight += 1
            else:
                bucket.loose += 1

        update(by_loose[loose])
        update(by_strict[strict_label])
        update(by_loose_and_c[(loose, c)])
        update(by_strict_and_c[(strict_label, c)])
        update(by_group_loose[row["group_struct"]])
        update(by_decomp[decomp])

        if total % 500 == 0:
            print(f"  ... {total} rows ({time.time() - t0:.1f}s)")

    print(f"\nTotal labeled rows: {total}, time {time.time() - t0:.1f}s")
    return {
        "by_loose": dict(by_loose),
        "by_strict": dict(by_strict),
        "by_loose_and_c": dict(by_loose_and_c),
        "by_strict_and_c": dict(by_strict_and_c),
        "by_group_loose": dict(by_group_loose),
        "by_decomp": dict(by_decomp),
    }


def report_bucket(label, b: Bucket):
    if b.total == 0:
        return
    nontriv = b.total - b.vacuous
    tr = 100.0 * b.tight / nontriv if nontriv > 0 else 0
    print(
        f"  {label:<35} total={b.total:>5} viol={len(b.violations):>5} "
        f"tight={b.tight:>5} loose={b.loose:>5} tight%={tr:>5.1f}%"
    )


def main():
    results = sweep()

    print("\n### By loose elementary-abelian classifier ###")
    for key, b in sorted(results["by_loose"].items()):
        report_bucket(f"is_g_odd_elem_ab = {key}", b)

    print("\n### By strict (single-prime) elementary-abelian classifier ###")
    for key, b in sorted(results["by_strict"].items()):
        report_bucket(key, b)

    print("\n### By loose elem-ab × c ###")
    for (loose, c), b in sorted(results["by_loose_and_c"].items()):
        label = f"elem_ab={loose} c={c}"
        report_bucket(label, b)

    print("\n### By strict elem-ab × c ###")
    for (strict, c), b in sorted(results["by_strict_and_c"].items()):
        label = f"{strict} c={c}"
        report_bucket(label, b)

    print("\n### By G_odd decomp ###")
    for decomp, b in sorted(results["by_decomp"].items()):
        label = f"decomp={decomp}"
        report_bucket(label, b)

    print("\n### Sample violations on loose elem-ab subset ###")
    sample = results["by_loose"][True].violations[:10] if True in results["by_loose"] else []
    for v in sample:
        print(
            f"  {v['instance_id'][:8]} {v['group_struct']} c={v['c']} "
            f"d={v['d']} bound={v['bound']} A={v['A_poly']!r}"
        )


if __name__ == "__main__":
    main()

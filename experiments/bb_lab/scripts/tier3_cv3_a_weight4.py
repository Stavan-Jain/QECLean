"""T3-A: spot-check the C-v3 narrowed conjecture on weight-4 BB codes
over Z_6 × Z_6.

HANDOFF_TIER3_CV3 §4 T3-A's full target is 50-200 in-scope instances,
but this script supports a `--limit` for a small sanity batch (10) that
runs in minutes rather than hours.

For each in-scope (A, B):
    1. Compute bound = bb_radical_bound(A, B, G)
    2. Compute d_exact via SAT (bounded by --max-d), with timeout
    3. Compare bound vs d_exact

Any violation (bound > d_exact) falsifies the narrowed conjecture on
weight-4 over Z_6 × Z_6.

Run:
    uv run python scripts/tier3_cv3_a_weight4.py --limit 10
"""

from __future__ import annotations

import argparse
import time
from itertools import islice

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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10,
                        help="Stop after this many in-scope instances (default 10)")
    parser.add_argument("--ell", type=int, default=6)
    parser.add_argument("--m", type=int, default=6)
    parser.add_argument("--weight", type=int, default=4)
    parser.add_argument("--max-d", type=int, default=12,
                        help="SAT distance upper bound (faster if d is small)")
    parser.add_argument("--timeout", type=int, default=60,
                        help="SAT timeout per instance (seconds)")
    parser.add_argument("--only-k-geq", type=int, default=2,
                        help="Drop instances with k < this (default 2)")
    args = parser.parse_args()

    G = ZmZn(args.ell, args.m)
    print(f"G = Z_{args.ell} × Z_{args.m}, n = 2|G| = {2 * G.cardinality}")
    print(f"is_g_odd_elementary_abelian(G) = {is_g_odd_elementary_abelian(G)}")
    print(f"weight = {args.weight}, max_d = {args.max_d}, limit = {args.limit}")
    print()

    in_scope: list[dict] = []
    enumerator = enumerate_canonical_pairs(
        G, weight=args.weight,
        only_k_geq=args.only_k_geq if args.only_k_geq > 0 else None,
    )
    pairs_seen = 0
    in_scope_seen = 0
    t_enum_start = time.time()
    for inst in enumerator:
        pairs_seen += 1
        A = Poly(group=G, support=inst.canonical.A_support)
        B = Poly(group=G, support=inst.canonical.B_support)
        c = joint_support_subgroup_index(A, B, G)
        if c < 3:
            continue
        in_scope_seen += 1
        bound = bb_radical_bound(A, B, G)
        in_scope.append({
            "A": A,
            "B": B,
            "c": c,
            "k": inst.k,
            "n": inst.n,
            "bound": bound,
            "A_str": A.canonical_string(),
            "B_str": B.canonical_string(),
        })
        if in_scope_seen >= args.limit:
            break
    print(
        f"Enumerated {pairs_seen} canonical weight-{args.weight} pairs "
        f"in {time.time() - t_enum_start:.1f}s "
        f"→ {in_scope_seen} in-scope (c ≥ 3)"
    )
    print()

    print(f"=== SAT-labeling {len(in_scope)} in-scope instances ===")
    violations: list[dict] = []
    tight = 0
    loose = 0
    for i, item in enumerate(in_scope):
        t0 = time.time()
        try:
            checks = bb_check_matrices(item["A"], item["B"])
            res = x_distance(
                checks,
                weight_upper_bound=args.max_d,
            )
            d_exact = res.distance
        except Exception as e:
            print(f"  [{i}] SAT error: {e}")
            continue
        dt = time.time() - t0
        if d_exact is None:
            verdict = "TIMEOUT"
        elif d_exact == 0 or d_exact < 0:
            verdict = f"unexpected d={d_exact}"
        elif item["bound"] > d_exact:
            violations.append({**item, "d_exact": d_exact})
            verdict = f"VIOLATION (bound {item['bound']} > d {d_exact})"
        elif item["bound"] == d_exact:
            tight += 1
            verdict = f"tight (bound = d = {d_exact})"
        else:
            loose += 1
            verdict = f"loose (bound {item['bound']} < d {d_exact}, gap {d_exact - item['bound']})"
        print(
            f"  [{i}] n={item['n']} k={item['k']} c={item['c']} "
            f"A={item['A_str']!r} B={item['B_str']!r}: "
            f"bound={item['bound']} d={d_exact} ({verdict}) [{dt:.1f}s]"
        )

    print()
    print("=== Summary ===")
    print(f"  in-scope tested: {len(in_scope)}")
    print(f"  violations:      {len(violations)}")
    print(f"  tight:           {tight}")
    print(f"  loose:           {loose}")
    if violations:
        print("\nVIOLATIONS — conjecture falsifies on weight-4 Z_6×Z_6:")
        for v in violations:
            print(
                f"  c={v['c']} A={v['A_str']!r} B={v['B_str']!r}: "
                f"bound={v['bound']} > d={v['d_exact']}"
            )


if __name__ == "__main__":
    main()

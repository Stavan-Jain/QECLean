"""Targeted test of H_UNIT² on Z_12 × Z_12 weight-3 A = x^3 + y^b + y^c.

Strategy to avoid heroic SAT:
- Pick a SMALL set of (b, c) pairs covering the (b mod 4, c mod 4) space.
- Set weight_upper_bound = 13.
  - H_UNIT² ✗ → predicted violator with d ≤ 12: SAT returns d, fast.
  - H_UNIT² ✓ → predicted tight with d = 18: SAT returns None at w ≤ 13.
    Distinguishes "tight" from "violator" without going heroic.

Decision rule:
  d returned ≤ 12 → confirmed violator (or smaller bound).
  d returned = None → d ≥ 14 → consistent with tight prediction.

Per-case predicted outcome based on H_UNIT²:
  H_UNIT² ✗ → expect d ≤ 12 (returned by SAT).
  H_UNIT² ✓ → expect d ≥ 14 (SAT timeout/None at cap=13).

Run:
    uv run python scripts/tier3_cv3_unit_squared_targeted.py --workers 4
"""

from __future__ import annotations

import argparse
import multiprocessing as mp
import time
from dataclasses import dataclass

from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.degeneracy import is_g_odd_elementary_abelian
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    joint_support_subgroup_index,
)
from bb_lab.sat_distance import x_distance


def lucas_mod2(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    return 1 if (k & n) == k else 0


def loewy_poly_from_g2(exps: list[int], axis_order: int) -> list[int]:
    coeffs = [0] * axis_order
    for b in exps:
        bk = b % axis_order
        for k in range(axis_order):
            coeffs[k] ^= lucas_mod2(bk, k)
    return coeffs


def loewy_depth(coeffs: list[int]) -> int:
    for k, c in enumerate(coeffs):
        if c:
            return k
    return len(coeffs)


def unit_factor_squared_is_one(coeffs: list[int]) -> bool:
    N = len(coeffs)
    nu = loewy_depth(coeffs)
    if nu == N:
        return True
    q = coeffs[nu:]
    if q[0] == 0:
        return True
    nq = len(q)
    u_sq = [0] * nq
    for i in range(nq):
        if i % 2 == 0:
            half = i // 2
            if half < nq:
                u_sq[i] = q[half]
    if u_sq[0] != 1:
        return False
    for i in range(1, nq):
        if u_sq[i] != 0:
            return False
    return True


B_STR = "y^3 + x + x^2"

# Targeted (b, c) pairs — ALL satisfy {b mod 3, c mod 3} = {1, 2} so
# A vanishes on cube-root orbits jointly with B (guaranteeing k > 0).
# Both H_UNIT² ✗ and ✓ signatures are covered.
#
#   H_UNIT² ✗ y-axis G_2 patterns (mod 4): (1,2), (0,3), or G_2-permutations
#   H_UNIT² ✓ y-axis G_2 patterns (mod 4): (2,3), (0,1), (0,2), (1,3)
TARGETED_BC = [
    # Format: (label, b, c, predicted)
    # H_UNIT² ✗ (predicted violators):
    ("C1 (1,2)",       1,  2, "✗ → viol"),   # mod4 (1,2), mod3 (1,2)
    ("(4,11)",         4, 11, "✗ → viol"),   # mod4 (0,3), mod3 (1,2)
    ("(5,10)",         5, 10, "✗ → viol"),   # mod4 (1,2), mod3 (2,1)
    # H_UNIT² ✓ (predicted tight):
    ("bb_288 (2,7)",   2,  7, "✓ → tight"),  # mod4 (2,3), mod3 (2,1)
    ("(4,5)",          4,  5, "✓ → tight"),  # mod4 (0,1), mod3 (1,2)
    ("(1,11)",         1, 11, "✓ → tight"),  # mod4 (1,3), mod3 (1,2)
]


@dataclass
class Spec:
    label: str
    b: int
    c: int
    pred: str
    weight_cap: int


@dataclass
class Result:
    label: str
    b: int
    c: int
    pred: str
    A_str: str
    weight_a: int
    cval: int
    odd_weight: bool
    in_domain: bool
    bound: int
    y_coeffs: list[int]
    y_depth: int
    h_unit2: bool
    n: int
    k: int
    d: int | None
    cap_hit: bool
    verdict: str
    elapsed: float


def worker(spec: Spec) -> Result:
    G = ZmZn(12, 12)
    A_str = f"x^3 + y^{spec.b} + y^{spec.c}"
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_STR, G)
    weight_a = len(A.support)
    cval = joint_support_subgroup_index(A, B, G)
    odd_w = (weight_a % 2 == 1) and (len(B.support) % 2 == 1)
    in_domain = is_g_odd_elementary_abelian(G) and cval >= 3 and odd_w

    y_coeffs = loewy_poly_from_g2([spec.b, spec.c], 4)
    y_depth = loewy_depth(y_coeffs)
    h_unit2 = unit_factor_squared_is_one(y_coeffs)

    t0 = time.time()
    try:
        checks = bb_check_matrices(A, B)
        params = code_params(checks)
        n, k = params.n, params.k
    except Exception:
        return Result(spec.label, spec.b, spec.c, spec.pred, A_str, weight_a,
                      cval, odd_w, in_domain, -1, y_coeffs, y_depth, h_unit2,
                      -1, -1, None, False, "error", time.time() - t0)
    if k == 0:
        return Result(spec.label, spec.b, spec.c, spec.pred, A_str, weight_a,
                      cval, odd_w, in_domain, -1, y_coeffs, y_depth, h_unit2,
                      n, 0, None, False, "k=0", time.time() - t0)

    bound = bb_radical_bound(A, B, G)
    try:
        res = x_distance(checks, weight_upper_bound=spec.weight_cap)
        d = res.distance
        cap_hit = False
    except Exception:
        d = None
        cap_hit = True

    if d is None:
        verdict = "d>cap"  # SAT exhausted w ≤ cap with no witness.
    elif not in_domain:
        verdict = "out"
    elif bound > d:
        verdict = "VIOLATION"
    elif bound == d:
        verdict = "tight"
    else:
        verdict = "loose"
    return Result(spec.label, spec.b, spec.c, spec.pred, A_str, weight_a,
                  cval, odd_w, in_domain, bound, y_coeffs, y_depth, h_unit2,
                  n, k, d, cap_hit, verdict, time.time() - t0)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--cap", type=int, default=13,
                    help="weight_upper_bound for SAT (default 13)")
    args = ap.parse_args()

    specs = [
        Spec(label, b, c, pred, args.cap)
        for (label, b, c, pred) in TARGETED_BC
    ]
    print(f"Targeted H_UNIT² test on Z_12 × Z_12, weight_upper_bound={args.cap}")
    print(f"Fixed B = {B_STR!r}, A = x^3 + y^b + y^c")
    print(f"Testing {len(specs)} (b, c) pairs:")
    for s in specs:
        print(f"  {s.label}: (b={s.b}, c={s.c}) — predicted {s.pred}")
    print()

    t0 = time.time()
    print(
        f"{'time':>6} {'label':<25} {'(b,c)':<8} {'y_coeffs':<14} "
        f"{'depth':>5} {'H_UNIT²':>8} {'bound':>5} {'d':>5} {'verdict':>10}",
        flush=True,
    )
    print("-" * 110, flush=True)

    results = []
    if args.workers <= 1:
        for s in specs:
            r = worker(s)
            results.append(r)
            d_str = "None" if r.d is None else str(r.d)
            print(
                f"{time.time()-t0:>6.0f} {r.label:<25} ({r.b},{r.c})   "
                f"{str(r.y_coeffs):<14} {r.y_depth:>5} {str(r.h_unit2):>8} "
                f"{r.bound:>5} {d_str:>5} {r.verdict:>10}",
                flush=True,
            )
    else:
        with mp.Pool(processes=args.workers) as pool:
            for r in pool.imap_unordered(worker, specs):
                results.append(r)
                d_str = "None" if r.d is None else str(r.d)
                print(
                    f"{time.time()-t0:>6.0f} {r.label:<25} ({r.b},{r.c})   "
                    f"{str(r.y_coeffs):<14} {r.y_depth:>5} {str(r.h_unit2):>8} "
                    f"{r.bound:>5} {d_str:>5} {r.verdict:>10}",
                    flush=True,
                )
        order = {s.label: i for i, s in enumerate(specs)}
        results.sort(key=lambda r: order[r.label])

    print(f"\nComputed {len(results)} in {time.time() - t0:.1f}s")

    print()
    print("### Prediction analysis ###")
    correct = wrong = 0
    for r in results:
        if not r.in_domain:
            continue
        if r.h_unit2:
            # Predicted tight: d should be ≥ cap+1 (= d>cap or actual d = bound).
            if r.verdict in ("tight", "d>cap"):
                correct += 1
                print(f"  ✓ {r.label}: H_UNIT² ✓ → {r.verdict} (matches tight prediction)")
            else:
                wrong += 1
                print(f"  ✗ {r.label}: H_UNIT² ✓ → {r.verdict} (predicted tight)")
        else:
            # Predicted violator: d should be ≤ cap and bound > d.
            if r.verdict == "VIOLATION":
                correct += 1
                print(f"  ✓ {r.label}: H_UNIT² ✗ → VIOLATION (matches viol prediction)")
            elif r.verdict in ("tight", "d>cap"):
                wrong += 1
                print(f"  ✗ {r.label}: H_UNIT² ✗ → {r.verdict} (predicted viol)")
            else:
                print(f"  ? {r.label}: H_UNIT² ✗ → {r.verdict} (predicted viol)")
    print()
    print(f"  Correct predictions: {correct}")
    print(f"  Wrong predictions:   {wrong}")
    if wrong == 0:
        print("  → H_UNIT² is a RELIABLE predictor on this sample")
    else:
        print("  → H_UNIT² has counterexamples; needs refinement")


if __name__ == "__main__":
    main()

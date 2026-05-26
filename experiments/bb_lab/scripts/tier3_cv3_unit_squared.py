"""Test H_UNIT² refinement on Z_12 × Z_12 weight-3 A = x^a + y^b + y^c.

H_UNIT² hypothesis (proposed): for each 2-Sylow axis i with |axis| ≥ 4, A's
per-axis G_2-projection has the form `(depth ν element) · u` where `u² = 1`
in the per-axis local ring.

In char 2, u² = 1 ⟺ u ∈ 1 + m_O² (where m_O = augmentation ideal).

For y-axis G_2 = Z_4 (= F_2[y']/(y'⁴)):
  A_y as polynomial in y':
    y'  bare       → u = 1, u² = 1 ✓
    y' · (1+y')   → u = 1+y', u² = 1+y'² ≠ 1 ✗
    y' · (1+y'²) → u = 1+y'², u² = 1 ✓
    y' · (1+y'³) → u = 1+y'³, u² = 1 ✓
    y'² · 1       → u = 1, u² = 1 ✓
    ...

For weight-3 A = x^a + y^b + y^c, the y-part is y^b + y^c with (b mod 4)
and (c mod 4) determining the y-axis G_2 polynomial.

This script:
1. Iterates (a, b, c) ∈ Z_12³ with a ≠ 0 (x-part), b ≠ c (distinct y-terms).
2. Computes A's y-axis G_2-projection in y'-basis.
3. Identifies u (the unit factor) and checks u² = 1.
4. Computes bound = bb_radical_bound, d via SAT.
5. Tests refined hypothesis (odd-weight ∧ H_UNIT²) and tabulates.

Parallelized over SAT.

Run:
    uv run python scripts/tier3_cv3_unit_squared.py --workers 4
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


# ---------------------------------------------------------------------------
# Loewy decomposition + u² check
# ---------------------------------------------------------------------------


def lucas_mod2(n: int, k: int) -> int:
    """C(n, k) mod 2 via Lucas: 1 iff (k & n) == k."""
    if k < 0 or k > n:
        return 0
    return 1 if (k & n) == k else 0


def loewy_poly_from_g2(exps: list[int], axis_order: int) -> list[int]:
    """Given y-exponents [b_1, ..., b_w] for a polynomial Σ y^{b_i}, return
    the y'-basis coefficients in F_2[y']/(y'^axis_order).

    Each y^b in F_2[Z_{axis_order}] (with y mod axis_order = b mod axis_order)
    equals [b_y^{b mod axis_order}] = (y'+1)^{b mod axis_order}
                                    = Σ_k Lucas(b mod axis_order, k) y'^k.

    Returns a list of length axis_order, entry k = coefficient of y'^k mod 2.
    """
    coeffs = [0] * axis_order
    for b in exps:
        bk = b % axis_order
        for k in range(axis_order):
            coeffs[k] ^= lucas_mod2(bk, k)
    return coeffs


def loewy_depth(coeffs: list[int]) -> int:
    """Smallest k with coeffs[k] != 0; len(coeffs) if all zero."""
    for k, c in enumerate(coeffs):
        if c:
            return k
    return len(coeffs)


def unit_factor_squared_is_one(coeffs: list[int]) -> bool:
    """For a polynomial in y'-basis (= F_2[y']/(y'^N) coefficients), check
    whether it factors as (depth-ν element) · u with u² = 1.

    Equivalently: write coeffs = y'^ν · q(y') where q has non-zero constant
    term. Then u = q · (q_0)^{-1} (normalize). Check u² = 1 in F_2[y']/(y'^{N-ν}).

    Simpler: u² = 1 iff (u-1)² = 0 iff (u-1) ∈ (y'^{ceil(N'/2)}) where N' is
    the residual nilpotency. Equivalent: u has y'-degree zero in odd-power
    coordinates of y'^(N'/2 .. N').

    For F_2[y']/(y'^N): u² = 1 iff u ∈ 1 + m_O^{ceil(N/2)}.
        - N=2 (Z_2): always u² = 1.
        - N=4 (Z_4): u² = 1 ⟺ u ∈ 1 + (y'²).
        - N=8 (Z_8): u² = 1 ⟺ u ∈ 1 + (y'⁴).

    But here we want to check u² = 1 within F_2[y']/(y'^{N-ν}). So the
    threshold depends on N - ν.

    Compute u by formal division: u = q / q[0]. Then verify u² = 1.
    """
    N = len(coeffs)
    nu = loewy_depth(coeffs)
    if nu == N:
        # All zero — no factorization. Vacuously satisfied (or undefined).
        return True
    # Extract q where coeffs = y'^ν · q, so q[i] = coeffs[ν + i] for i in [0, N-ν).
    q = coeffs[nu:]
    # q[0] must be non-zero (= 1 in F_2). Verify.
    if q[0] == 0:
        # Shouldn't happen given nu = loewy_depth.
        return True
    # u = q (in F_2, q[0]=1 already).
    # Check u² = 1 in F_2[y']/(y'^{N-ν}).
    # u² has coefficients: (u²)[i] = sum_{j} u[j] · u[i-j].
    # In char 2, (u²)[i] = u[i/2] if i even else 0.
    nq = len(q)
    u_sq = [0] * nq
    for i in range(nq):
        if i % 2 == 0:
            half = i // 2
            if half < nq:
                u_sq[i] = q[half]
    # u² = 1 iff u_sq == [1, 0, 0, ..., 0].
    if u_sq[0] != 1:
        return False
    for i in range(1, nq):
        if u_sq[i] != 0:
            return False
    return True


# ---------------------------------------------------------------------------
# SAT worker
# ---------------------------------------------------------------------------


@dataclass
class Spec:
    a: int
    b: int
    c: int


@dataclass
class Result:
    a: int
    b: int
    c: int
    A_str: str
    B_str: str
    weight_a: int
    cval: int
    elem_ab: bool
    odd_weight: bool
    bound: int
    n: int
    k: int
    d: int | None
    verdict: str
    y_coeffs: list[int]
    y_depth: int
    y_u_sq_one: bool
    x_coeffs: list[int]
    x_depth: int
    x_u_sq_one: bool
    elapsed: float
    note: str = ""


B_STR = "y^3 + x + x^2"


def worker(spec: Spec) -> Result:
    G = ZmZn(12, 12)
    a, b, c = spec.a, spec.b, spec.c
    A_str = f"x^{a} + y^{b} + y^{c}"
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_STR, G)
    weight_a = len(A.support)
    cval = joint_support_subgroup_index(A, B, G)
    elem_ab = is_g_odd_elementary_abelian(G)
    odd_w = (weight_a % 2 == 1) and (len(B.support) % 2 == 1)

    # Per-axis Loewy decomposition on Z_4 (G_2 axes have order 4 each).
    # A's y-exponents: {b, c}. A's x-exponents: {a}.
    y_coeffs = loewy_poly_from_g2([b, c], 4)
    x_coeffs = loewy_poly_from_g2([a], 4)
    y_depth = loewy_depth(y_coeffs)
    x_depth = loewy_depth(x_coeffs)
    y_u_sq_one = unit_factor_squared_is_one(y_coeffs)
    x_u_sq_one = unit_factor_squared_is_one(x_coeffs)

    t0 = time.time()
    try:
        checks = bb_check_matrices(A, B)
        params = code_params(checks)
        n, k = params.n, params.k
    except Exception as e:
        return Result(a, b, c, A_str, B_STR, weight_a, cval, elem_ab, odd_w,
                      -1, -1, -1, None, "error", y_coeffs, y_depth, y_u_sq_one,
                      x_coeffs, x_depth, x_u_sq_one, time.time() - t0,
                      note=f"code_params: {e}")
    if k == 0:
        return Result(a, b, c, A_str, B_STR, weight_a, cval, elem_ab, odd_w,
                      -1, n, 0, None, "k=0", y_coeffs, y_depth, y_u_sq_one,
                      x_coeffs, x_depth, x_u_sq_one, time.time() - t0,
                      note="k=0")

    bound = bb_radical_bound(A, B, G)
    in_domain = elem_ab and cval >= 3 and odd_w  # C-v3.1 refined hypothesis

    try:
        res = x_distance(checks, weight_upper_bound=20)
        d = res.distance
    except Exception as e:
        return Result(a, b, c, A_str, B_STR, weight_a, cval, elem_ab, odd_w,
                      bound, n, k, None, "sat_error", y_coeffs, y_depth, y_u_sq_one,
                      x_coeffs, x_depth, x_u_sq_one, time.time() - t0,
                      note=f"SAT: {e}")
    if not in_domain:
        verdict = "out"
    elif bound > d:
        verdict = "VIOLATION"
    elif bound == d:
        verdict = "tight"
    else:
        verdict = "loose"
    return Result(a, b, c, A_str, B_STR, weight_a, cval, elem_ab, odd_w,
                  bound, n, k, d, verdict, y_coeffs, y_depth, y_u_sq_one,
                  x_coeffs, x_depth, x_u_sq_one, time.time() - t0)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()

    # Build spec list: (a, b, c) with a ∈ {1..11}, b < c ∈ {0..11}, b ≠ c.
    # Restrict to a small set for the spot check — focus on a = 3 (gross-style x-part),
    # vary (b, c) over the y-axis space.
    specs: list[Spec] = []
    for b in range(12):
        for c in range(b + 1, 12):
            specs.append(Spec(a=3, b=b, c=c))
    print(f"Enumerating {len(specs)} (a=3, b<c) pairs on Z_12 × Z_12 …")
    print(f"Fixed B = {B_STR!r}, fixed a = 3.")
    print()

    t0 = time.time()
    if args.workers <= 1:
        results = [worker(s) for s in specs]
    else:
        with mp.Pool(processes=args.workers) as pool:
            results = list(pool.imap_unordered(worker, specs))
        order = {(s.a, s.b, s.c): i for i, s in enumerate(specs)}
        results.sort(key=lambda r: order[(r.a, r.b, r.c)])
    print(f"Computed {len(results)} results in {time.time() - t0:.1f}s")

    # Filter to in-domain (C-v3.1: elem_ab ∧ c ≥ 3 ∧ odd-weight).
    in_domain = [r for r in results if r.elem_ab and r.cval >= 3 and r.odd_weight
                 and r.d is not None]
    print(f"In-domain (C-v3.1): {len(in_domain)} of {len(results)}")
    print()

    print(
        f"{'(a,b,c)':<10} {'y_coeffs':<14} {'y_dep':>5} {'y_u²=1':>7} "
        f"{'x_coeffs':<14} {'x_dep':>5} {'x_u²=1':>7} "
        f"{'k':>3} {'c':>3} {'bound':>5} {'d':>3} {'verdict':>10}"
    )
    print("-" * 130)
    h_unit2_predictions: dict[bool, dict[str, int]] = {
        True: {"VIOLATION": 0, "tight": 0, "loose": 0},
        False: {"VIOLATION": 0, "tight": 0, "loose": 0},
    }
    for r in in_domain:
        h_unit2 = r.y_u_sq_one and r.x_u_sq_one
        h_unit2_predictions[h_unit2][r.verdict] += 1
        marker = "★" if r.verdict == "VIOLATION" else " "
        print(
            f"{marker}({r.a},{r.b},{r.c}) "
            f"{str(r.y_coeffs):<14} {r.y_depth:>5} {str(r.y_u_sq_one):>7} "
            f"{str(r.x_coeffs):<14} {r.x_depth:>5} {str(r.x_u_sq_one):>7} "
            f"{r.k:>3} {r.cval:>3} {r.bound:>5} {r.d:>3} {r.verdict:>10}"
        )

    print()
    print("### H_UNIT² prediction summary (within C-v3.1 in-domain) ###")
    print(f"{'H_UNIT²':<10} {'VIOLATION':>10} {'tight':>10} {'loose':>10}")
    for cond in [True, False]:
        cnt = h_unit2_predictions[cond]
        print(
            f"{str(cond):<10} {cnt['VIOLATION']:>10} {cnt['tight']:>10} {cnt['loose']:>10}"
        )

    print()
    print("### Conclusion ###")
    # H_UNIT² succeeds if all VIOLATIONS have H_UNIT² = False AND
    # all tight/loose have H_UNIT² = True (or, more permissively, just
    # all VIOLATIONS have H_UNIT² = False).
    v_false = h_unit2_predictions[False]["VIOLATION"]
    v_true = h_unit2_predictions[True]["VIOLATION"]
    print(f"  Violations with H_UNIT² = True (BAD for refinement):  {v_true}")
    print(f"  Violations with H_UNIT² = False (GOOD; excluded):     {v_false}")
    if v_true == 0:
        print("  → H_UNIT² + C-v3.1 excludes ALL in-domain violators ✓")
    else:
        print(f"  → H_UNIT² + C-v3.1 still admits {v_true} violators ✗")


if __name__ == "__main__":
    main()

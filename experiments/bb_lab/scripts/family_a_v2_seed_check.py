"""Family A v2 — Step 1+2: implement and verify `a_O_spread`.

The H_UNIT² failure note (notes/T3_CV3_H_UNIT2_attempt.md §"Why H_UNIT² is
incomplete") observed: for the four C-v3.1 cases on Z_12 × Z_12, tight
instances have 3 nonzero y'-coefficients in `a_O`; violators have 1-2.

This script:
  1. Implements `a_O_y_spread(poly, G, orbit_rep)` → number of nonzero
     y'-only entries (x' = 0, y' > 0) in a_O's projection.
  2. Reproduces the four-case table from T3_CV3_H_UNIT2_attempt to
     confirm the literature note matches what the code computes.

If Step 2 confirms the four values, Step 3 (broader corpus check)
follows in a separate script.
"""

from __future__ import annotations

from bb_lab.algebraic_features import (
    _project_poly_to_R_O,
)
from bb_lab.group import ZmZn
from bb_lab.poly import Poly


def _binom_mod2(n: int, k: int) -> int:
    """C(n, k) mod 2 via Lucas's theorem: 1 iff (k & n) == k bitwise."""
    if k < 0 or k > n:
        return 0
    return 1 if (k & n) == k else 0


def _to_loewy_basis(
    a_O_dict: dict[tuple[int, ...], list[int]],
    n_2s: tuple[int, ...],
    r: int,
) -> dict[tuple[int, ...], list[int]]:
    """Change basis from monomial `x_1^{a_1} ... x_k^{a_k}` to Loewy
    `(x_1+1)^{i_1} ... (x_k+1)^{i_k}`.

    In characteristic 2, monomial → Loewy via:
       x^a = sum_{i=0}^{a} C(a, i) · (x+1)^i.
    For a tensor of axes, the coefficient at Loewy index (i_1, ..., i_k)
    is sum over (a_1, ..., a_k) with a_j >= i_j of
    prod_j C(a_j, i_j) · standard_coeff(a_1, ..., a_k), all mod 2 in
    the F_{2^r} arithmetic.
    """
    k = len(n_2s)
    loewy: dict[tuple[int, ...], list[int]] = {}
    for std_idx, coeff in a_O_dict.items():
        if not any(coeff):
            continue
        # Enumerate all Loewy indices i ≤ a (componentwise).
        ranges = [range(a + 1) for a in std_idx]
        from itertools import product
        for loewy_idx in product(*ranges):
            # binomial product mod 2
            mult = 1
            for axis in range(k):
                mult &= _binom_mod2(std_idx[axis], loewy_idx[axis])
            if not mult:
                continue
            # XOR-add `coeff` into loewy[loewy_idx]
            if loewy_idx in loewy:
                loewy[loewy_idx] = [a ^ b for a, b in zip(loewy[loewy_idx], coeff)]
            else:
                loewy[loewy_idx] = coeff[:]
    return loewy


def a_O_y_spread(A: Poly, G: ZmZn, orbit_rep: tuple[int, ...]) -> int:
    """Number of nonzero pure-y' Loewy-basis entries in `a_O` =
    proj_{R_O}(A), expanded in the Loewy basis `(x+1)^i (y+1)^j`.

    "Pure y'" means Loewy index (0, j) with j > 0 and nonzero F_{2^r}
    coefficient. This matches T3_CV3_H_UNIT2_attempt.md's example
    expansions like `x' + x'² + x'³ + y' + ω²·y'² + ω²·y'³` where the
    y'-only support is {y', y'², y'³} → cardinality 3.
    """
    a_O_dict, r, prim_poly, n_2s = _project_poly_to_R_O(A, G, orbit_rep)
    loewy = _to_loewy_basis(a_O_dict, n_2s, r)
    count = 0
    for loewy_idx, coeff in loewy.items():
        # Pure y': x'-component (axis 0) is 0, y'-component (axis 1) > 0.
        if loewy_idx[0] != 0:
            continue
        if len(loewy_idx) < 2 or loewy_idx[1] == 0:
            continue
        if any(coeff):
            count += 1
    return count


def main() -> None:
    G = ZmZn(12, 12)

    # The four test cases from T3_CV3_H_UNIT2_attempt §"Why H_UNIT² is incomplete".
    # All share B = y³ + x + x²; only A's exponents vary.
    cases = [
        ("(4, 5)",     "x^3 + y^4 + y^5",     1, "VIOLATION (bound=18, d=12)"),
        ("(1, 2)  C1", "x^3 + y + y^2",       2, "VIOLATION (bound=18, d=12)"),
        ("(1, 11)",    "x^3 + y + y^11",      3, "tight (bound=12, d=12)"),
        ("(2, 7) ≈ bb_288 sister", "x^3 + y^2 + y^7", 3, "tight (expected)"),
    ]

    # Orbit (1, 1) on G_odd = Z_3 × Z_3 is the cube-root orbit that
    # C-v3.1 lives on. Use the per-axis odd-quotient representative.
    orbit_rep = (1, 1)
    print(f"Testing a_O_y_spread at orbit O = {orbit_rep} on G = Z_12 × Z_12")
    print(f"{'case':30s} {'predicted':10s} {'computed':10s}  {'verdict-from-note'}")
    for label, poly_str, predicted, verdict in cases:
        A = Poly.from_string(poly_str, G)
        observed = a_O_y_spread(A, G, orbit_rep)
        match = "✓" if observed == predicted else "✗"
        print(f"  {label:28s}   {predicted:<5d}      {observed:<5d} {match}   {verdict}")


if __name__ == "__main__":
    main()

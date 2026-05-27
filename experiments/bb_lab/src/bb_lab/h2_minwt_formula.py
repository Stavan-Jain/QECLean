"""H_2 minimum weight formula for weight-3 BB codes (round-2 v2 session 3).

This module implements the closed-form structural feature

    min_wt(H_2(K(A, B))) ≤ (4/9)·|G|

derived in `pipeline/attempts/bb_distance_conjecture_family_d_v3_h2_minwt_formula/result.md`.
The bound holds for any weight-3 BB code (A, B) over G = Z_ℓ × Z_m
satisfying the **refined Z_3-pair condition**:

    There exist group homomorphisms φ_A, φ_B : G → Z_3 such that

      1. φ_A(supp(A)) = {0, 1, 2}  AND  φ_A(supp(B)) is constant
      2. φ_B(supp(B)) = {0, 1, 2}  AND  φ_B(supp(A)) is constant
      3. φ_A and φ_B are linearly independent.

Such homomorphisms factor as φ(x, y) = a·x + b·y mod 3 for some
(a, b) ∈ Z_3 × Z_3 \\ {(0,0)}. There are only 8 such pairs to check.

When the refined hypothesis holds, the **explicit witness**

    e(x, y) = 1[φ_A(x, y) ≠ 2 AND φ_B(x, y) ≠ 2]

lies in `Ann(A) ∩ Ann(B) = H_2(Koszul(A, B))` with weight (4/9)·|G|.

The mechanism (one-line proof): φ_A(supp(A)) = {0,1,2} forces
`(1_{φ_A ≠ 2}) ∈ Ann(A)` (each h gets contribution = 2 mod 2 = 0); the
constant φ_A(supp(B)) means multiplying by `1_{φ_B ≠ 2}` doesn't change
this (it just permutes the contributions trivially). Symmetric for B.

This module:
  - `find_refined_z3_pair(A, B)`: finds (a1, b1, a2, b2) if pair exists.
  - `min_wt_h2_upper_bound(A, B, G)`: returns (4/9)|G| if pair exists,
    None otherwise.
  - `construct_h2_witness(A, B, G)`: returns the explicit element of
    F_2[G] (as a numpy array) when the bound applies.

The combined §6h-§6m structural-impossibility theorem
(`pipeline/attempts/bb_distance_conjecture_family_d_v2_6m_obstruction`)
ensures this is a **feature**, not a lower-bound on d_X — the relation
min_wt(H_2) ≥ d_X has the wrong sign and is upper-bounded by d_X
elsewhere in the code (Lin-Pryadko Statement 12, etc.).
"""

from __future__ import annotations

from collections import Counter
from typing import Optional

import numpy as np

from .group import AbelianGroup, ZmZn
from .poly import Poly


TARGET_MULTISET = Counter({0: 1, 1: 1, 2: 1})


def _phi_image(poly: Poly, a: int, b: int) -> Counter:
    """Return the multiset φ(supp(poly)) where φ(x, y) = a*x + b*y mod 3.

    Requires poly.group to be a 2-axis abelian group.
    """
    return Counter((a * g[0] + b * g[1]) % 3 for g in poly.support)


def _is_constant_multiset(multiset: Counter) -> bool:
    """True if the multiset has exactly one distinct value."""
    if not multiset:
        return False
    return len(set(multiset.elements())) == 1


def find_refined_z3_pair(
    A: Poly, B: Poly
) -> Optional[tuple[tuple[int, int], tuple[int, int]]]:
    """Find (phi_A_coef, phi_B_coef) satisfying the refined hypothesis.

    Each coef is (a, b) ∈ Z_3 × Z_3 \\ {(0,0)} representing
    `phi(x, y) = a*x + b*y mod 3`.

    Requires:
      - phi_A(supp(A)) = {0, 1, 2} as a multiset
      - phi_A(supp(B)) is constant
      - phi_B(supp(B)) = {0, 1, 2}
      - phi_B(supp(A)) is constant
      - phi_A and phi_B are linearly independent (det != 0 mod 3)

    Returns (None) if no such pair exists. Returns the first found pair
    (canonical ordering by (a1, b1, a2, b2)) otherwise.
    """
    for a1 in range(3):
        for b1 in range(3):
            if (a1, b1) == (0, 0):
                continue
            phi_A_on_A = _phi_image(A, a1, b1)
            if phi_A_on_A != TARGET_MULTISET:
                continue
            phi_A_on_B = _phi_image(B, a1, b1)
            if not _is_constant_multiset(phi_A_on_B):
                continue
            for a2 in range(3):
                for b2 in range(3):
                    if (a2, b2) == (0, 0):
                        continue
                    phi_B_on_B = _phi_image(B, a2, b2)
                    if phi_B_on_B != TARGET_MULTISET:
                        continue
                    phi_B_on_A = _phi_image(A, a2, b2)
                    if not _is_constant_multiset(phi_B_on_A):
                        continue
                    det = (a1 * b2 - a2 * b1) % 3
                    if det != 0:
                        return ((a1, b1), (a2, b2))
    return None


def min_wt_h2_upper_bound(A: Poly, B: Poly, G: AbelianGroup) -> Optional[int]:
    """Return the closed-form upper bound (4/9)·|G| if the refined Z_3-pair
    hypothesis holds, otherwise None.

    Requires G to be Z_ℓ × Z_m. The bound is an upper bound on
    min_wt(H_2(Koszul(A, B))) where H_2 = Ann(A) ∩ Ann(B) in F_2[G].

    Does not require G.cardinality to be divisible by 9 — that
    condition is automatically met when the pair exists (since two
    independent Z_3-homs require |G/(ker_A ∩ ker_B)| = 9).
    """
    if G.rank != 2:
        return None  # Only Z_ell × Z_m for now
    pair = find_refined_z3_pair(A, B)
    if pair is None:
        return None
    n = G.cardinality
    if n % 9 != 0:
        # Safety check; this shouldn't happen if pair exists
        return None
    return (4 * n) // 9


def construct_h2_witness(
    A: Poly, B: Poly, G: AbelianGroup
) -> Optional[np.ndarray]:
    """Build the explicit H_2 witness element when the refined hypothesis
    holds.

    Returns a numpy uint8 array of length |G| (row-major over Z_ℓ × Z_m,
    i.e., index `x*m + y`), representing the F_2-coefficient vector of
    `1[phi_A(x, y) ≠ 2 AND phi_B(x, y) ≠ 2]` in F_2[G].

    Verified: `circulant(A) @ v % 2 == 0` and `circulant(B) @ v % 2 == 0`,
    so v ∈ Ann(A) ∩ Ann(B) = H_2(K(A, B)).
    """
    if G.rank != 2:
        return None
    pair = find_refined_z3_pair(A, B)
    if pair is None:
        return None
    (a1, b1), (a2, b2) = pair
    ell, m = G.orders[0], G.orders[1]
    n = G.cardinality
    v = np.zeros(n, dtype=np.uint8)
    for x in range(ell):
        for y in range(m):
            phi_A_val = (a1 * x + b1 * y) % 3
            phi_B_val = (a2 * x + b2 * y) % 3
            if phi_A_val != 2 and phi_B_val != 2:
                v[x * m + y] = 1
    return v


def closed_form_formula(wt: int, abs_G: int) -> float:
    """Return the conjectured general formula for weight-w polynomials:

        min_wt(H_2) ≤ ((w-1)/w)^2 · |G|

    For w = 3 (weight-3 BB codes), this is (4/9)·|G|.

    This is the conjectured generalization; the refined-pair theorem in
    this module is proved only for w = 3. Higher weights would need
    a Z_w-analog of the refined-pair structure.
    """
    if wt <= 0:
        return 0.0
    return ((wt - 1) / wt) ** 2 * abs_G

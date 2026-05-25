"""BB-code check matrices.

This module is the **single source of truth** for the H_X / H_Z encoding.
It must agree bitwise with the Lean side
([QEC/Stabilizer/Framework/Homological/BBChainComplex.lean]) on the
convolution convention:

    conv A f g = ∑_h A(h) · f(g − h)        (over F₂[G])

so the circulant operator `M_A` (multiplication by A) is the |G|×|G|
matrix `M_A[g, h] = A(g − h)`. The BB-code check matrices are then

    H_X = [ M_A  |  M_B  ]                  (|G| × 2|G|, X-stabilizer rows)
    H_Z = [ M_Bᵀ |  M_Aᵀ ]                  (|G| × 2|G|, Z-stabilizer rows)

CSS commutation `H_X · H_Zᵀ = 0` follows from `M_A · M_B + M_B · M_A = 0`
over char 2 because the underlying group G is abelian
(`bbBoundary_comp` in the Lean file).

Row/column ordering uses `AbelianGroup.index` (row-major); we are free
to choose any consistent enumeration since the Lean side does not pin
one. `tests/test_gross_agreement.py` verifies a few hand-derived
entries against the convolution definition to catch index errors.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .group import AbelianGroup
from .poly import Poly


@dataclass(frozen=True, slots=True)
class CheckMatrices:
    """Dense uint8 check matrices for a BB code over `group`.

    `H_X` and `H_Z` are both shape (|G|, 2|G|) with entries in {0, 1}.
    The first |G| columns form the "A-block" (i.e. qubit index
    `(group_element, 0)` in the Lean `C₁ = G × Fin 2` decomposition),
    the last |G| the "B-block" (`(group_element, 1)`).
    """

    group: AbelianGroup
    H_X: np.ndarray  # shape (|G|, 2|G|), dtype uint8
    H_Z: np.ndarray  # shape (|G|, 2|G|), dtype uint8

    @property
    def num_qubits(self) -> int:
        return 2 * self.group.cardinality


def circulant(poly: Poly) -> np.ndarray:
    """Return the |G|×|G| dense uint8 matrix `M[g, h] = poly(g − h)`.

    The Lean side calls this `conv poly · -` viewed as a linear map.
    """
    G = poly.group
    n = G.cardinality
    M = np.zeros((n, n), dtype=np.uint8)
    elems = list(G)  # canonical row-major order matching G.index
    for r, g in enumerate(elems):
        for c, h in enumerate(elems):
            if G.sub(g, h) in poly.support:
                M[r, c] = 1
    return M


def bb_check_matrices(A: Poly, B: Poly) -> CheckMatrices:
    """Build H_X and H_Z for a BB code with polynomials A, B over the
    same abelian group G."""
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
    G = A.group
    M_A = circulant(A)
    M_B = circulant(B)
    # H_X = [M_A | M_B]
    H_X = np.concatenate([M_A, M_B], axis=1)
    # H_Z = [M_Bᵀ | M_Aᵀ]
    H_Z = np.concatenate([M_B.T, M_A.T], axis=1)
    assert H_X.shape == (G.cardinality, 2 * G.cardinality)
    assert H_Z.shape == (G.cardinality, 2 * G.cardinality)
    return CheckMatrices(group=G, H_X=H_X.astype(np.uint8), H_Z=H_Z.astype(np.uint8))


def assert_css_commutation(checks: CheckMatrices) -> None:
    """Hard guard: H_X · H_Zᵀ ≡ 0 (mod 2).

    Run at construction time in v0 tests; cheap (n=288 → 0.05 s).
    """
    prod = checks.H_X @ checks.H_Z.T
    if np.any(prod % 2 != 0):
        bad = np.argwhere(prod % 2 != 0)
        raise AssertionError(
            f"H_X · H_Zᵀ has {len(bad)} non-zero entries mod 2; "
            f"first offender: row {bad[0, 0]}, col {bad[0, 1]} = {prod[bad[0, 0], bad[0, 1]]}"
        )

"""Verify the Lab's gross-code H_X / H_Z agree with the Lean truth.

The "Lean truth" is the literal definition of `grossA` / `grossB` in
[pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean:52]
(see also B_lifted_product/attempt.lean):

    def grossA : GrossGroup → ZMod 2
      | (3, 0) => 1
      | (0, 1) => 1
      | (0, 2) => 1
      | _      => 0

    def grossB : GrossGroup → ZMod 2
      | (0, 3) => 1
      | (1, 0) => 1
      | (2, 0) => 1
      | _      => 0

together with the `BBChainComplex.lean` convolution convention

    conv A f g = ∑_h A(h) · f(g − h)        →     M_A[g, h] = A(g − h)

and the BB check-matrix layout `H_X = [M_A | M_B]`, `H_Z = [M_Bᵀ | M_Aᵀ]`.

The test:
  (1) parses the polynomial strings out of `pipeline/attempts/gross/state.yaml`
      via the Lab parser;
  (2) asserts the parsed supports equal the hardcoded Lean-truth supports
      (so a parser bug fails here);
  (3) asserts every entry of H_X and H_Z matches an independent oracle
      computed directly from the supports + the conv definition (so a
      matrix-construction bug fails here).

If a future change makes the Lab and Lean disagree on the encoding, this
test is the canary.
"""

from __future__ import annotations

import numpy as np

from bb_lab.checks import assert_css_commutation, bb_check_matrices
from bb_lab.group import ZmZn
from bb_lab.poly import Poly


# Lean-truth supports from `grossA`, `grossB` pattern-match definitions.
LEAN_GROSS_A_SUPPORT: frozenset[tuple[int, int]] = frozenset({(3, 0), (0, 1), (0, 2)})
LEAN_GROSS_B_SUPPORT: frozenset[tuple[int, int]] = frozenset({(0, 3), (1, 0), (2, 0)})
LEAN_GROSS_ELL = 12
LEAN_GROSS_M = 6


def test_state_yaml_parses_to_lean_supports(gross_state_yaml):
    """Step 1+2: parser fidelity vs Lean truth."""
    assert gross_state_yaml["group"] == "Z_12 x Z_6"
    G = ZmZn(LEAN_GROSS_ELL, LEAN_GROSS_M)

    A = Poly.from_string(gross_state_yaml["polynomials"]["A"], G)
    B = Poly.from_string(gross_state_yaml["polynomials"]["B"], G)

    assert A.support == LEAN_GROSS_A_SUPPORT, (
        f"parser disagrees with Lean grossA: got {sorted(A.support)}"
    )
    assert B.support == LEAN_GROSS_B_SUPPORT, (
        f"parser disagrees with Lean grossB: got {sorted(B.support)}"
    )


def _independent_circulant(supp: frozenset[tuple[int, int]], G) -> np.ndarray:
    """Build M[g, h] = 1 iff (g − h) ∈ supp, completely independently
    of `bb_lab.checks.circulant`."""
    n = G.cardinality
    M = np.zeros((n, n), dtype=np.uint8)
    elems = list(G)
    for r, g in enumerate(elems):
        for c, h in enumerate(elems):
            diff = ((g[0] - h[0]) % G.orders[0], (g[1] - h[1]) % G.orders[1])
            if diff in supp:
                M[r, c] = 1
    return M


def test_gross_HX_HZ_bitwise_match_oracle(gross_state_yaml):
    """Step 3: matrix-construction agreement, bitwise."""
    G = ZmZn(LEAN_GROSS_ELL, LEAN_GROSS_M)
    A = Poly.from_string(gross_state_yaml["polynomials"]["A"], G)
    B = Poly.from_string(gross_state_yaml["polynomials"]["B"], G)
    checks = bb_check_matrices(A, B)

    M_A_oracle = _independent_circulant(LEAN_GROSS_A_SUPPORT, G)
    M_B_oracle = _independent_circulant(LEAN_GROSS_B_SUPPORT, G)
    H_X_oracle = np.concatenate([M_A_oracle, M_B_oracle], axis=1)
    H_Z_oracle = np.concatenate([M_B_oracle.T, M_A_oracle.T], axis=1)

    assert checks.H_X.shape == H_X_oracle.shape == (72, 144)
    assert checks.H_Z.shape == H_Z_oracle.shape == (72, 144)
    assert np.array_equal(checks.H_X, H_X_oracle), (
        "Lab H_X disagrees with conv-oracle on gross code"
    )
    assert np.array_equal(checks.H_Z, H_Z_oracle), (
        "Lab H_Z disagrees with conv-oracle on gross code"
    )


def test_gross_check_weights():
    """Every row of H_X has exactly weight(A) + weight(B) = 6 ones (BB invariant)."""
    G = ZmZn(LEAN_GROSS_ELL, LEAN_GROSS_M)
    A = Poly.from_support(LEAN_GROSS_A_SUPPORT, G)
    B = Poly.from_support(LEAN_GROSS_B_SUPPORT, G)
    checks = bb_check_matrices(A, B)
    row_weights_X = checks.H_X.sum(axis=1)
    row_weights_Z = checks.H_Z.sum(axis=1)
    assert (row_weights_X == 6).all()
    assert (row_weights_Z == 6).all()
    # Column weights also match (transposed roles)
    col_weights_X = checks.H_X.sum(axis=0)
    assert (col_weights_X == 3).all(), (
        "Each qubit participates in exactly 3 X-checks for BB(weight-3 polys)"
    )


def test_gross_CSS_commutation():
    """H_X · H_Zᵀ ≡ 0 (mod 2) — this is `bbBoundary_comp` on the Lean side."""
    G = ZmZn(LEAN_GROSS_ELL, LEAN_GROSS_M)
    A = Poly.from_support(LEAN_GROSS_A_SUPPORT, G)
    B = Poly.from_support(LEAN_GROSS_B_SUPPORT, G)
    checks = bb_check_matrices(A, B)
    assert_css_commutation(checks)

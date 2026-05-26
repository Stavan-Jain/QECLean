"""Tests for the support-generates-G degeneracy classifier.

The test cases hit:
  * Gross's `grossA` and `grossB` — both generate `Z_12 × Z_6` (non-degenerate).
  * `1 + y + y²` on `Z_3 × Z_5` — degenerate (generates only `{0} × Z_5`).
  * The polynomial `1` (constant) — degenerate (generates `{0}`).
  * `1 + x + y` on `Z_3 × Z_5` — non-degenerate (single-step coverage).
  * Edge case: zero polynomial — degenerate.
  * `1 + x²` on `Z_4` — degenerate (generates `{0, 2} ≤ Z_4`, index 2).

Each test pins both the boolean classifier and the index diagnostic
so that future refactors of `_subgroup_closure` don't drift silently.
"""

from __future__ import annotations

from bb_lab.degeneracy import (
    is_non_degenerate,
    supp_generates_G,
    support_subgroup_index,
)
from bb_lab.group import AbelianGroup, ZmZn
from bb_lab.poly import Poly


# ---------------------------------------------------------------------------
# Gross polynomials — the canonical non-degenerate reference
# ---------------------------------------------------------------------------


def test_gross_polynomials_are_degenerate_under_strict_definition():
    """Bravyi's gross polynomials on Z_12 × Z_6: each has subgroup-index 3.

    `supp(grossA) = {(3,0), (0,1), (0,2)}`. The closure under
    addition is `⟨(3,0)⟩ × Z_6 = {0,3,6,9} × Z_6`, of size 24 and
    index `72 / 24 = 3` in Z_12 × Z_6.

    Same for `supp(grossB) = {(0,3), (1,0), (2,0)}` by symmetry.

    Under the spec's strict non-degeneracy condition
    `⟨supp(A)⟩ = G AND ⟨supp(B)⟩ = G`, gross is therefore
    **degenerate**. (Under the looser joint condition
    `⟨supp(A) ∪ supp(B)⟩ = G`, gross IS non-degenerate, since the
    union closure equals the full Z_12 × Z_6 — see T3R2.4 §3.)

    This test pins the empirical truth under the strict definition,
    which is what `is_non_degenerate(A, B, G)` implements.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)

    # supp(A) generates a subgroup of order 24, index 3 in Z_12 × Z_6.
    assert support_subgroup_index(A, G) == 3
    assert support_subgroup_index(B, G) == 3
    assert not supp_generates_G(A, G)
    assert not supp_generates_G(B, G)
    assert not is_non_degenerate(A, B, G)


# ---------------------------------------------------------------------------
# Spec-prescribed cases
# ---------------------------------------------------------------------------


def test_single_axis_poly_on_Z3_x_Z5_is_degenerate():
    """`1 + y + y²` on Z_3 × Z_5 only touches the y-axis.

    supp = {(0,0), (0,1), (0,2)}. The closure under addition is
    `{0} × Z_5` (size 5), index 3. Classic single-axis degeneracy.
    """
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + y + y^2", G)

    assert support_subgroup_index(A, G) == 3
    assert not supp_generates_G(A, G)


def test_trivial_polynomial_is_degenerate():
    """`1` on any nontrivial G generates only `{0}`.

    supp = {(0,0)}; closure = `{(0,0)}`; index = |G|. Maximum
    degeneracy.
    """
    G = ZmZn(3, 5)
    A = Poly.from_string("1", G)

    assert support_subgroup_index(A, G) == 15  # |Z_3 × Z_5| = 15
    assert not supp_generates_G(A, G)


def test_diagonal_poly_on_Z3_x_Z5_is_non_degenerate():
    """`1 + x + y` on Z_3 × Z_5 generates the full group.

    supp = {(0,0), (1,0), (0,1)}. `(1,0)` alone generates `Z_3 × {0}`
    (size 3); `(0,1)` alone generates `{0} × Z_5` (size 5); together
    they generate `Z_3 × Z_5`. Index = 1.
    """
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + y", G)

    assert support_subgroup_index(A, G) == 1
    assert supp_generates_G(A, G)


def test_is_non_degenerate_requires_both():
    """`is_non_degenerate(A, B, G)` requires BOTH supports to generate G."""
    G = ZmZn(3, 5)
    A_ok = Poly.from_string("1 + x + y", G)  # non-degenerate
    A_bad = Poly.from_string("1 + y + y^2", G)  # y-axis only

    assert is_non_degenerate(A_ok, A_ok, G)
    assert not is_non_degenerate(A_ok, A_bad, G)
    assert not is_non_degenerate(A_bad, A_ok, G)
    assert not is_non_degenerate(A_bad, A_bad, G)


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------


def test_zero_polynomial_is_degenerate():
    """Zero polynomial (empty support) generates only `{0}`."""
    G = ZmZn(3, 5)
    A = Poly.zero(G)

    assert support_subgroup_index(A, G) == 15
    assert not supp_generates_G(A, G)


def test_index_2_subgroup_on_Z4():
    """`1 + x²` on Z_4 generates `{0, 2}` of index 2."""
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x^2", G)

    # supp = {(0,), (2,)}; closure adds (2,)+(2,)=(0,), stops. size 2.
    assert support_subgroup_index(A, G) == 2
    assert not supp_generates_G(A, G)


def test_full_group_via_single_generator():
    """`1 + x` on Z_4 generates the full Z_4 (since 1 has order 4)."""
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x", G)

    assert support_subgroup_index(A, G) == 1
    assert supp_generates_G(A, G)


def test_two_axis_full_coverage():
    """`x + y` on Z_3 × Z_3 (no constant) — does (1,0) + (0,1) span?

    `(1,0)` generates `Z_3 × {0}`; `(0,1)` generates `{0} × Z_3`;
    together they span `Z_3 × Z_3`. Index = 1.
    """
    G = ZmZn(3, 3)
    A = Poly.from_string("x + y", G)

    assert support_subgroup_index(A, G) == 1
    assert supp_generates_G(A, G)


# ---------------------------------------------------------------------------
# Lagrange consistency: index always divides |G|
# ---------------------------------------------------------------------------


def test_index_divides_group_order_on_assorted_polys():
    """Across a small sweep, support_subgroup_index always divides |G|.

    This is a sanity check on `_subgroup_closure`: a buggy closure
    that misses some closures would produce a fractional "index".
    """
    samples = [
        (ZmZn(3, 5), "1 + x + y"),
        (ZmZn(3, 5), "1 + y + y^2"),
        (ZmZn(12, 6), "x^3 + y + y^2"),
        (ZmZn(6, 6), "1 + x^2 + y^4"),
        (ZmZn(4, 6), "x^2 + y^3"),
        (AbelianGroup((9,)), "1 + x^3 + x^6"),
        (AbelianGroup((8,)), "1 + x^4"),
    ]
    for G, s in samples:
        A = Poly.from_string(s, G)
        idx = support_subgroup_index(A, G)
        assert G.cardinality % idx == 0, (
            f"{s} on {G.label()}: index {idx} doesn't divide |G|={G.cardinality}"
        )

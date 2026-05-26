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
    g_odd_decomposition,
    g_odd_elementary_prime,
    is_g_odd_elementary_abelian,
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


# ===========================================================================
# C-v3: elementary-abelian G_odd classifier tests
# ===========================================================================


def test_g_odd_decomposition_gross():
    """Gross G = Z_12 × Z_6 has G_odd = Z_3 × Z_3 (cube-root × cube-root)."""
    assert g_odd_decomposition(ZmZn(12, 6)) == (3, 3)


def test_g_odd_decomposition_bb108():
    """bb_108 G = Z_9 × Z_6 has G_odd = Z_9 × Z_3 — the Z_9 makes it
    NOT elementary abelian (per HANDOFF_C3 §1)."""
    assert g_odd_decomposition(ZmZn(9, 6)) == (3, 9)


def test_g_odd_decomposition_bb90():
    """bb_90 G = Z_15 × Z_3 is odd-order; G_odd = G itself decomposes
    via CRT into Z_3 × Z_5 × Z_3 (axis 1 splits into Z_3 × Z_5)."""
    assert g_odd_decomposition(ZmZn(15, 3)) == (3, 3, 5)


def test_g_odd_decomposition_z4xz6():
    """Z_4 × Z_6: axis 1 odd part = 1 (Z_4 is a 2-group), axis 2 odd
    part = 3. G_odd = Z_3, rank 1."""
    assert g_odd_decomposition(ZmZn(4, 6)) == (3,)


def test_g_odd_decomposition_z4_pure_2group():
    """Z_4 is a 2-group; G_odd is trivial."""
    assert g_odd_decomposition(AbelianGroup((4,))) == ()


def test_is_g_odd_elementary_abelian_bravyi_table():
    """The 5 Bravyi codes: 4 are loose-elementary-abelian, 1 is not.

    HANDOFF_C3 §1: bb_108 (G_odd = Z_9 × Z_3) is the only Bravyi instance
    failing the hypothesis. The other 4 must qualify.
    """
    # bb_72, gross, bb_288: G_odd = Z_3 × Z_3
    assert is_g_odd_elementary_abelian(ZmZn(6, 6)) is True
    assert is_g_odd_elementary_abelian(ZmZn(12, 6)) is True
    assert is_g_odd_elementary_abelian(ZmZn(12, 12)) is True
    # bb_90: G_odd = Z_3 × Z_3 × Z_5 (multi-prime but each part elem-ab)
    assert is_g_odd_elementary_abelian(ZmZn(15, 3)) is True
    # bb_108: NOT elementary abelian (has Z_9 factor)
    assert is_g_odd_elementary_abelian(ZmZn(9, 6)) is False


def test_is_g_odd_elementary_abelian_2group():
    """A 2-group has trivial G_odd → vacuously elementary abelian."""
    assert is_g_odd_elementary_abelian(AbelianGroup((4,))) is True
    assert is_g_odd_elementary_abelian(AbelianGroup((4, 2))) is True


def test_is_g_odd_elementary_abelian_rank1():
    """Single-cyclic-G_odd is elementary abelian (rank 1).

    Per HANDOFF_C3 §C-v3.4, Z_4 × Z_6 (G_odd = Z_3) qualifies — this
    resolves the Z_4 × Z_6 anomaly: it's already in the loose-elem-ab
    domain.
    """
    assert is_g_odd_elementary_abelian(ZmZn(4, 6)) is True  # G_odd = Z_3
    assert is_g_odd_elementary_abelian(ZmZn(3, 4)) is True  # G_odd = Z_3
    assert is_g_odd_elementary_abelian(ZmZn(8, 6)) is True  # G_odd = Z_3


def test_g_odd_elementary_prime_strict():
    """Strict single-prime classifier."""
    assert g_odd_elementary_prime(ZmZn(12, 6)) == 3   # (Z_3)^2
    assert g_odd_elementary_prime(ZmZn(15, 3)) is None  # multi-prime (3, 5)
    assert g_odd_elementary_prime(ZmZn(9, 6)) is None   # Z_9 factor
    assert g_odd_elementary_prime(AbelianGroup((4,))) is None  # trivial
    assert g_odd_elementary_prime(ZmZn(5, 5)) == 5   # (Z_5)^2
    assert g_odd_elementary_prime(AbelianGroup((7,))) == 7  # Z_7

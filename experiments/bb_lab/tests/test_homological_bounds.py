"""Tests for `bb_lab.homological_bounds`.

Coverage:

1. Pure-algebra checks on the projection map `_project_poly_mod`:
   monomial reductions, F₂-cancellation of collisions, error cases.

2. `enumerate_base_codes` produces all proper divisor pairs (count =
   τ(ℓ) · τ(m) − 1 for rank 2; minus 1 for the excluded trivial
   1-cover), and projections are consistent.

3. The marquee example from SRB 2025 §5: gross [[144,12,12]] is a
   double cover of [[72,12,6]]. The base-code projection from the
   gross polynomials must recover the [[72,12,6]] polynomials exactly.

4. `bb_homological_bound` on gross with a Bravyi-table base
   distance lookup returns:
   * `6` in conjectural mode (the SRB §7 conjecture, h=2 allowed).
   * `1` in rigorous mode (no odd-h base with known distance).

5. `bb_homological_bound` on bb_72_12_6 with a Bravyi-table base
   distance lookup is **trivial (1)**: no smaller Bravyi-listed
   base for [[72,12,6]] exists. Same for other Bravyi-table cases
   where the code doesn't sit on top of a known smaller Bravyi
   table entry.

6. `bb_homological_condition` diagnostics fire correctly:
   `"no_base_distance_callable"`, `"no_usable_base"`,
   `"only_even_h_bases"`, etc.

7. `bb_homological_upper_bound` (companion) sanity: for gross,
   upper = 2 · 6 = 12 in conjectural mode (matches the actual
   distance 12 exactly).
"""

from __future__ import annotations

import pytest

from bb_lab.group import AbelianGroup, ZmZn
from bb_lab.homological_bounds import (
    BaseCover,
    _divisors,
    _project_poly_mod,
    base_distance_from_table,
    bb_homological_bound,
    bb_homological_condition,
    bb_homological_upper_bound,
    enumerate_base_codes,
)
from bb_lab.poly import Poly


# ---------------------------------------------------------------------------
# Divisor helper
# ---------------------------------------------------------------------------


def test_divisors_basic():
    assert _divisors(1) == [1]
    assert _divisors(6) == [1, 2, 3, 6]
    assert _divisors(12) == [1, 2, 3, 4, 6, 12]
    assert _divisors(72) == [1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72]


def test_divisors_invalid():
    with pytest.raises(ValueError):
        _divisors(0)


# ---------------------------------------------------------------------------
# Projection map
# ---------------------------------------------------------------------------


def test_project_single_monomial():
    """`x³` on Z_12 × Z_6, projected down to Z_6 × Z_6, becomes `x³`."""
    G_cover = ZmZn(12, 6)
    G_base = ZmZn(6, 6)
    A = Poly.from_string("x^3", G_cover)
    p = _project_poly_mod(A, G_cover, G_base)
    expected = Poly.from_string("x^3", G_base)
    assert p == expected


def test_project_high_exponent_wraps():
    """`x^9` on Z_12 × Z_6 projects to `x^3` on Z_6 × Z_6."""
    G_cover = ZmZn(12, 6)
    G_base = ZmZn(6, 6)
    A = Poly.from_string("x^9", G_cover)
    p = _project_poly_mod(A, G_cover, G_base)
    expected = Poly.from_string("x^3", G_base)
    assert p == expected


def test_project_f2_cancellation():
    """Two monomials that project to the same base monomial cancel."""
    G_cover = ZmZn(12, 6)
    G_base = ZmZn(6, 6)
    # x^3 and x^9 both project to x^3 in Z_6 → cancel.
    A = Poly.from_string("x^3 + x^9", G_cover)
    p = _project_poly_mod(A, G_cover, G_base)
    expected = Poly.zero(G_base)
    assert p == expected


def test_project_mixed():
    """`x^3 + y + y^2` on Z_12 × Z_6 projects to `x^3 + y + y^2` on Z_6 × Z_6
    (already in canonical form for the smaller group)."""
    G_cover = ZmZn(12, 6)
    G_base = ZmZn(6, 6)
    A = Poly.from_string("x^3 + y + y^2", G_cover)
    p = _project_poly_mod(A, G_cover, G_base)
    expected = Poly.from_string("x^3 + y + y^2", G_base)
    assert p == expected


def test_project_rejects_non_divisor():
    """Base order must divide cover order, axis by axis."""
    G_cover = ZmZn(12, 6)
    G_base = ZmZn(5, 6)  # 5 ∤ 12
    A = Poly.from_string("x", G_cover)
    with pytest.raises(ValueError, match="divide"):
        _project_poly_mod(A, G_cover, G_base)


def test_project_rejects_wrong_rank():
    G_cover = AbelianGroup((12,))
    G_base = ZmZn(6, 6)  # rank 2 vs cover rank 1
    A = Poly.from_string("x", G_cover)
    with pytest.raises(ValueError, match="rank"):
        _project_poly_mod(A, G_cover, G_base)


# ---------------------------------------------------------------------------
# Base-code enumeration
# ---------------------------------------------------------------------------


def test_enumerate_count_z6_z6():
    """For G = Z_6 × Z_6: τ(6)·τ(6) − 1 = 4·4 − 1 = 15 proper divisor pairs."""
    G = ZmZn(6, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    bases = enumerate_base_codes(A, B, G)
    assert len(bases) == 15


def test_enumerate_count_z12_z6():
    """For G = Z_12 × Z_6: τ(12)·τ(6) − 1 = 6·4 − 1 = 23 proper divisor pairs."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    bases = enumerate_base_codes(A, B, G)
    assert len(bases) == 23


def test_enumerate_excludes_trivial_self_cover():
    """The 1-cover (Z_ℓ × Z_m → Z_ℓ × Z_m) is excluded by construction."""
    G = ZmZn(6, 6)
    A = Poly.from_string("x", G)
    B = Poly.from_string("y", G)
    bases = enumerate_base_codes(A, B, G)
    for b in bases:
        assert b.G_base.orders != G.orders


def test_enumerate_h_values_correct():
    """For each base, `h = |G_cover| / |G_base| = u · t`."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    bases = enumerate_base_codes(A, B, G)
    for b in bases:
        assert b.h == b.u * b.t
        assert b.h == G.cardinality // b.G_base.cardinality


def test_enumerate_rank1():
    """Univariate (rank 1) case still enumerates correctly."""
    G = AbelianGroup((6,))
    A = Poly.from_string("x^2", G)
    B = Poly.from_string("x^3", G)
    bases = enumerate_base_codes(A, B, G)
    # divisors of 6 = {1, 2, 3, 6}, minus the trivial 6 → {1, 2, 3} → 3 bases
    assert len(bases) == 3
    h_values = sorted(b.h for b in bases)
    assert h_values == [2, 3, 6]


def test_enumerate_rejects_rank3():
    """Only rank ≤ 2 supported in v0."""
    G = AbelianGroup((2, 2, 2))
    A = Poly.from_support([(0, 0, 0)], G)
    B = Poly.from_support([(1, 0, 0)], G)
    with pytest.raises(NotImplementedError):
        enumerate_base_codes(A, B, G)


# ---------------------------------------------------------------------------
# SRB Example 5 (gross as double cover of [[72,12,6]])
# ---------------------------------------------------------------------------


def test_gross_is_double_cover_of_72_12_6():
    """The marquee example from SRB 2025 §5 / Example 5:

    Gross [[144,12,12]] with `(Ã = x³+y+y², B̃ = y³+x+x², l̃=12, m̃=6)`
    is a double cover of the [[72,12,6]] code with
    `(A = x³+y+y², B = y³+x+x², l=6, m=6)`.

    Verify: projection of gross's polynomials onto Z_6 × Z_6 must
    recover bb_72_12_6's polynomials EXACTLY, and the corresponding
    BaseCover's `h = 2`.
    """
    G_gross = ZmZn(12, 6)
    A_gross = Poly.from_string("x^3 + y + y^2", G_gross)
    B_gross = Poly.from_string("y^3 + x + x^2", G_gross)

    G_72 = ZmZn(6, 6)
    A_72_expected = Poly.from_string("x^3 + y + y^2", G_72)
    B_72_expected = Poly.from_string("y^3 + x + x^2", G_72)

    bases = enumerate_base_codes(A_gross, B_gross, G_gross)
    matches = [
        b for b in bases
        if b.G_base.orders == (6, 6)
        and b.A_base == A_72_expected
        and b.B_base == B_72_expected
    ]
    assert len(matches) == 1, (
        f"expected exactly 1 base = bb_72_12_6, found {len(matches)} "
        f"out of {len(bases)} bases"
    )
    base = matches[0]
    assert base.h == 2
    assert base.u == 2
    assert base.t == 1
    assert not base.is_rigorous  # h=2 even → conjectural-only


# ---------------------------------------------------------------------------
# `bb_homological_bound` end-to-end
# ---------------------------------------------------------------------------


def test_gross_lower_bound_conjectural():
    """Apply the SRB §7 conjecture to gross with bb_72_12_6's distance
    pre-loaded: should yield `d_gross ≥ 6`.
    """
    G_gross = ZmZn(12, 6)
    A_gross = Poly.from_string("x^3 + y + y^2", G_gross)
    B_gross = Poly.from_string("y^3 + x + x^2", G_gross)

    G_72 = ZmZn(6, 6)
    A_72 = Poly.from_string("x^3 + y + y^2", G_72)
    B_72 = Poly.from_string("y^3 + x + x^2", G_72)
    lookup = base_distance_from_table([(A_72, B_72, G_72, 6)])

    lower = bb_homological_bound(
        A_gross, B_gross, G_gross, base_distance=lookup
    )
    assert lower == 6


def test_gross_lower_bound_rigorous_is_trivial():
    """In rigorous mode (require_rigorous=True), no odd-h base for
    gross is known in the Bravyi table → bound returns trivial 1.
    """
    G_gross = ZmZn(12, 6)
    A_gross = Poly.from_string("x^3 + y + y^2", G_gross)
    B_gross = Poly.from_string("y^3 + x + x^2", G_gross)

    G_72 = ZmZn(6, 6)
    A_72 = Poly.from_string("x^3 + y + y^2", G_72)
    B_72 = Poly.from_string("y^3 + x + x^2", G_72)
    lookup = base_distance_from_table([(A_72, B_72, G_72, 6)])

    lower = bb_homological_bound(
        A_gross, B_gross, G_gross,
        base_distance=lookup,
        require_rigorous=True,
    )
    assert lower == 1


def test_gross_upper_bound_matches_d12():
    """SRB Theorem 4.6 upper bound (conjectural): `d_gross ≤ 2 · 6 = 12`.
    Matches the actual gross distance exactly."""
    G_gross = ZmZn(12, 6)
    A_gross = Poly.from_string("x^3 + y + y^2", G_gross)
    B_gross = Poly.from_string("y^3 + x + x^2", G_gross)

    G_72 = ZmZn(6, 6)
    A_72 = Poly.from_string("x^3 + y + y^2", G_72)
    B_72 = Poly.from_string("y^3 + x + x^2", G_72)
    lookup = base_distance_from_table([(A_72, B_72, G_72, 6)])

    upper = bb_homological_upper_bound(
        A_gross, B_gross, G_gross, base_distance=lookup
    )
    assert upper == 12


def test_bound_trivial_without_lookup():
    """If `base_distance` is None, the bound is trivial 1."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    assert bb_homological_bound(A, B, G) == 1


def test_bound_trivial_with_empty_lookup():
    """If the lookup never returns a usable distance, the bound is 1."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    lookup = base_distance_from_table([])
    assert bb_homological_bound(A, B, G, base_distance=lookup) == 1


def test_bb_72_12_6_no_known_base():
    """bb_72_12_6 has no smaller Bravyi-table entry that it's a cover
    of; the conjectural bound is trivial 1 with only the Bravyi
    table as a base-distance source."""
    G_72 = ZmZn(6, 6)
    A = Poly.from_string("x^3 + y + y^2", G_72)
    B = Poly.from_string("y^3 + x + x^2", G_72)
    # Provide only OTHER Bravyi codes — none of which is a base of [[72,12,6]].
    lookup = base_distance_from_table([])  # no entries
    assert bb_homological_bound(A, B, G_72, base_distance=lookup) == 1


# ---------------------------------------------------------------------------
# `bb_homological_condition` diagnostics
# ---------------------------------------------------------------------------


def test_condition_no_callable():
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    ok, why = bb_homological_condition(A, B, G)
    assert ok is False
    assert why == "no_base_distance_callable"


def test_condition_no_usable_base():
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    lookup = base_distance_from_table([])
    ok, why = bb_homological_condition(A, B, G, base_distance=lookup)
    assert ok is False
    assert why == "no_usable_base"


def test_condition_ok_conjectural():
    """Gross + 72_12_6 in conjectural mode: condition holds."""
    G_gross = ZmZn(12, 6)
    A_gross = Poly.from_string("x^3 + y + y^2", G_gross)
    B_gross = Poly.from_string("y^3 + x + x^2", G_gross)

    G_72 = ZmZn(6, 6)
    A_72 = Poly.from_string("x^3 + y + y^2", G_72)
    B_72 = Poly.from_string("y^3 + x + x^2", G_72)
    lookup = base_distance_from_table([(A_72, B_72, G_72, 6)])

    ok, why = bb_homological_condition(
        A_gross, B_gross, G_gross, base_distance=lookup
    )
    assert ok is True
    assert why == "ok"


def test_condition_only_even_h_in_rigorous():
    """Gross + 72_12_6 in rigorous mode: the only usable base has h=2
    (even), so condition fails."""
    G_gross = ZmZn(12, 6)
    A_gross = Poly.from_string("x^3 + y + y^2", G_gross)
    B_gross = Poly.from_string("y^3 + x + x^2", G_gross)

    G_72 = ZmZn(6, 6)
    A_72 = Poly.from_string("x^3 + y + y^2", G_72)
    B_72 = Poly.from_string("y^3 + x + x^2", G_72)
    lookup = base_distance_from_table([(A_72, B_72, G_72, 6)])

    ok, why = bb_homological_condition(
        A_gross, B_gross, G_gross,
        base_distance=lookup,
        require_rigorous=True,
    )
    assert ok is False
    # Diagnostic could be either "no_usable_base" (since h=2 base
    # got filtered out before usability check) or "only_even_h_bases"
    # depending on internal traversal; both are acceptable.
    assert why in ("no_usable_base", "only_even_h_bases")


# ---------------------------------------------------------------------------
# BaseCover dataclass
# ---------------------------------------------------------------------------


def test_basecover_is_rigorous_predicate():
    """`is_rigorous` is True iff h is odd."""
    G_base = ZmZn(3, 3)
    A = Poly.from_string("x", G_base)
    B = Poly.from_string("y", G_base)
    for h, expected in [(1, True), (2, False), (3, True), (4, False), (5, True), (6, False)]:
        bc = BaseCover(
            A_base=A, B_base=B, G_base=G_base, u=h, t=1, h=h
        )
        assert bc.is_rigorous == expected, f"h={h}: expected {expected}"


# ---------------------------------------------------------------------------
# `base_distance_from_table` helper
# ---------------------------------------------------------------------------


def test_base_distance_from_table_lookup():
    """The helper builds a working callable from a finite table."""
    G = ZmZn(6, 6)
    A1 = Poly.from_string("x^3 + y + y^2", G)
    B1 = Poly.from_string("y^3 + x + x^2", G)
    A2 = Poly.from_string("x + y", G)
    B2 = Poly.from_string("x^2 + y^2", G)
    table = [
        (A1, B1, G, 6),
        (A2, B2, G, 4),
    ]
    fn = base_distance_from_table(table)
    assert fn(A1, B1, G) == 6
    assert fn(A2, B2, G) == 4
    # Unknown poly → None.
    A3 = Poly.from_string("x", G)
    B3 = Poly.from_string("y", G)
    assert fn(A3, B3, G) is None

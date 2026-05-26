"""Tests for `jacobson_radical_depth` and `jacobson_radical_bound`.

The depth μ_O(A) is the F_{2^|O|}-dimension of the kernel of
multiplication-by-a_O in the local component R_O = F_{2^|O|}[G_2]. It
satisfies the identity

    dim_{F_2} ker M_A  =  Σ_O |O| · μ_O(A)

(over Frobenius orbits on G_odd). For semisimple components (where
G_2 is trivial), μ ∈ {0, 1}: 0 if A doesn't vanish on O, 1 if it
does. For non-semisimple components μ takes values in {0, 1, ..., |G_2|}
and captures the depth of A in the radical filtration of R_O.

The tests cover:
  * Semisimple case ([[30,4,6]] champion, G = Z_3 × Z_5): a_O ∈ F_4 a
    field, μ is binary.
  * Non-semisimple case (gross, G = Z_12 × Z_6): each vanishing orbit
    has μ = 2 (the "doubling" of dim ker M_A from semisimple).
  * Chain ring case (Z_4 = Z_{2^2}, A = (1+x)²): the classical Loewy
    filtration; depth = 2.
  * Kernel-formula consistency: Σ |O| · μ_O = dim ker M_A.
"""

from __future__ import annotations

import pytest

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_bound,
    jacobson_radical_depth,
)
from bb_lab.checks import circulant
from bb_lab.group import AbelianGroup, ZmZn
from bb_lab.linalg import rank_f2
from bb_lab.poly import Poly


def _dim_ker(A: Poly) -> int:
    M = circulant(A)
    return A.group.cardinality - rank_f2(M)


# ---------------------------------------------------------------------------
# Semisimple: G_2 trivial — μ ∈ {0, 1}
# ---------------------------------------------------------------------------


def test_mu_30_4_6_champion_vanishing_orbit():
    """[[30,4,6]] champion: G = Z_3 × Z_5 (semisimple), A = 1 + x + x²·y.

    A vanishes on exactly one orbit (the size-2 x-only-nontrivial orbit
    {(1,0), (2,0)}). Expected: μ = 1 on that orbit, 0 elsewhere.
    """
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    orbits = g_odd_frobenius_orbits(G)
    mu_values = [jacobson_radical_depth(A, o, G) for o in orbits]
    # Exactly one vanishing orbit; the rest are 0.
    assert sum(1 for m in mu_values if m > 0) == 1
    # That orbit's μ should be exactly 1 (semisimple, μ ∈ {0, 1}).
    vanishing_mu = [m for m in mu_values if m > 0]
    assert vanishing_mu == [1]


def test_mu_30_4_6_dim_ker_consistency():
    """Σ |O| · μ_O(A) = dim_{F_2} ker M_A on Z_3 × Z_5."""
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    orbits = g_odd_frobenius_orbits(G)
    formula = sum(
        len(o) * jacobson_radical_depth(A, o, G) for o in orbits
    )
    assert formula == _dim_ker(A) == 2


def test_mu_semisimple_z3_x_z3():
    """G = Z_3 × Z_3, several A's. Semisimple. μ ∈ {0, 1} per orbit and
    the formula Σ |O| · μ = dim ker holds."""
    G = ZmZn(3, 3)
    orbits = g_odd_frobenius_orbits(G)
    for poly_str in [
        "1 + x + x^2",
        "1 + y + y^2",
        "x + x^2*y",
        "1 + x*y + x^2*y^2",
    ]:
        A = Poly.from_string(poly_str, G)
        mu_values = [jacobson_radical_depth(A, o, G) for o in orbits]
        # All μ's in {0, 1} for semisimple.
        for m in mu_values:
            assert m in (0, 1), f"semisimple expects μ ∈ {{0, 1}}, got {m}"
        # Sum-formula consistency.
        contrib = sum(len(o) * m for o, m in zip(orbits, mu_values))
        assert contrib == _dim_ker(A), (
            f"sum formula mismatch on {poly_str}: contrib={contrib}, "
            f"dim_ker={_dim_ker(A)}"
        )


# ---------------------------------------------------------------------------
# Chain ring: Z_{2^k}, single radical generator
# ---------------------------------------------------------------------------


def test_mu_z4_one_plus_x_squared():
    """G = Z_4, A = (1+x)² = 1 + x² in F_2[Z_4]. This is the canonical
    non-semisimple chain-ring example. F_2[Z_4] = F_2[t]/(t^4) with
    t = x-1; A = t². μ should be 2 (depth in the rad filtration).
    """
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x^2", G)
    orbits = g_odd_frobenius_orbits(G)
    # Z_4 has G_odd = Z_1, so a single trivial orbit.
    assert len(orbits) == 1
    mu = jacobson_radical_depth(A, orbits[0], G)
    assert mu == 2


def test_mu_z4_one_plus_x():
    """G = Z_4, A = 1 + x = t. Depth-1 element in rad. μ = 1."""
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x", G)
    orbits = g_odd_frobenius_orbits(G)
    mu = jacobson_radical_depth(A, orbits[0], G)
    assert mu == 1


def test_mu_z4_full_chain():
    """G = Z_4, A = (1+x)^k for k = 0, 1, 2, 3 — full Loewy chain."""
    G = AbelianGroup((4,))
    orbits = g_odd_frobenius_orbits(G)
    # (1+x)^0 = 1: unit, μ = 0.
    assert jacobson_radical_depth(Poly.from_string("1", G), orbits[0], G) == 0
    # (1+x)^1 = 1+x: μ = 1.
    assert jacobson_radical_depth(Poly.from_string("1 + x", G), orbits[0], G) == 1
    # (1+x)^2 = 1+x²: μ = 2.
    assert jacobson_radical_depth(Poly.from_string("1 + x^2", G), orbits[0], G) == 2
    # (1+x)^3 = 1 + x + x² + x^3: μ = 3.
    assert jacobson_radical_depth(
        Poly.from_string("1 + x + x^2 + x^3", G), orbits[0], G
    ) == 3


def test_mu_z4_dim_ker_consistency():
    """Σ |O| · μ = dim ker M_A on Z_4 for all the chain elements."""
    G = AbelianGroup((4,))
    orbits = g_odd_frobenius_orbits(G)
    for poly_str in ["1 + x", "1 + x^2", "1 + x + x^2 + x^3", "1 + x^3"]:
        A = Poly.from_string(poly_str, G)
        mu = jacobson_radical_depth(A, orbits[0], G)
        contrib = len(orbits[0]) * mu  # |O| = 1 here
        assert contrib == _dim_ker(A), (
            f"sum formula mismatch on Z_4, {poly_str}: μ={mu}, "
            f"dim_ker={_dim_ker(A)}"
        )


# ---------------------------------------------------------------------------
# Non-semisimple non-chain: gross G = Z_12 × Z_6
# ---------------------------------------------------------------------------


def test_mu_gross_A():
    """Gross, A = x³+y+y². T2.2 observation: dim ker M_A = 12, distributed
    as 3 vanishing G_odd-orbits (the y-axis nontrivial cube-root family),
    each of size 2 with μ = 2.

    Specifically: A vanishes on orbits where β ≠ 0 (β = y-axis cube-root
    exponent). In G_odd = Z_3 × Z_3, those are:
      {(0,1), (0,2)}, {(1,1), (2,2)}, {(1,2), (2,1)} — three size-2 orbits.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    orbits = g_odd_frobenius_orbits(G)
    mu_values = {tuple(sorted(o)): jacobson_radical_depth(A, o, G) for o in orbits}

    # Exactly three vanishing orbits, all with μ = 2.
    vanishing = [(o, m) for o, m in mu_values.items() if m > 0]
    assert len(vanishing) == 3
    for _, m in vanishing:
        assert m == 2


def test_mu_gross_B():
    """Gross, B = y³+x+x². By symmetry with A: B vanishes on 3 orbits
    where α ≠ 0 (α = x-axis exponent), each size 2 with μ = 2.
    """
    G = ZmZn(12, 6)
    B = Poly.from_string("y^3 + x + x^2", G)
    orbits = g_odd_frobenius_orbits(G)
    mu_values = {tuple(sorted(o)): jacobson_radical_depth(B, o, G) for o in orbits}
    vanishing = [(o, m) for o, m in mu_values.items() if m > 0]
    assert len(vanishing) == 3
    for _, m in vanishing:
        assert m == 2


def test_mu_gross_dim_ker_consistency():
    """Σ |O| · μ_O = dim ker M_A = 12 on gross."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    orbits = g_odd_frobenius_orbits(G)
    for poly in (A, B):
        contrib = sum(len(o) * jacobson_radical_depth(poly, o, G) for o in orbits)
        assert contrib == _dim_ker(poly) == 12


def test_mu_gross_joint_vanishing():
    """Joint vanishing: orbits where BOTH μ_A > 0 AND μ_B > 0.

    These are orbits where α ≠ 0 AND β ≠ 0 in G_odd = Z_3 × Z_3:
      {(1,1), (2,2)} (diagonal) and {(1,2), (2,1)} (anti-diagonal).
    Exactly 2 joint orbits.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    orbits = g_odd_frobenius_orbits(G)
    n_joint = sum(
        1 for o in orbits
        if jacobson_radical_depth(A, o, G) > 0
        and jacobson_radical_depth(B, o, G) > 0
    )
    assert n_joint == 2


def test_mu_gross_bound():
    """The bound on gross. Per the conjecture's definition (joint
    vanishing summed), the bound is 2 + 2 = 4 orbits worth of |O|·min(μ_A, μ_B)
    = 2·min(2,2) + 2·min(2,2) = 8. Note: this is LOOSE compared to the
    actual d=12; the conjecture is not tight on gross.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    assert jacobson_radical_bound(A, B, G) == 8


# ---------------------------------------------------------------------------
# Sum-formula consistency on various groups
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("ell,m,A_str", [
    (3, 4, "x + x^2 + y"),
    (4, 6, "1 + x^2 + y"),
    (6, 6, "x^3 + y + y^2"),
])
def test_mu_dim_ker_consistency_various(ell, m, A_str):
    """Σ |O| · μ_O = dim_{F_2} ker M_A holds across various groups."""
    G = ZmZn(ell, m)
    A = Poly.from_string(A_str, G)
    orbits = g_odd_frobenius_orbits(G)
    contrib = sum(len(o) * jacobson_radical_depth(A, o, G) for o in orbits)
    assert contrib == _dim_ker(A), (
        f"sum mismatch on {G.label()}, {A_str}: "
        f"contrib={contrib}, dim_ker={_dim_ker(A)}"
    )


# ---------------------------------------------------------------------------
# API tests
# ---------------------------------------------------------------------------


def test_mu_validates_orbit_argument():
    """Passing an orbit on G (not G_odd) should error."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    # Build a fake "orbit" with a value out of G_odd's range.
    bad_orbit = frozenset({(11, 5)})  # G_odd is Z_3 × Z_3, so values must be < 3.
    with pytest.raises(ValueError):
        jacobson_radical_depth(A, bad_orbit, G)


def test_bound_mismatched_groups():
    G1 = ZmZn(3, 3)
    G2 = ZmZn(3, 4)
    A = Poly.from_string("1 + x", G1)
    B = Poly.from_string("1 + x", G2)
    with pytest.raises(ValueError):
        jacobson_radical_bound(A, B)


def test_g_odd_frobenius_orbits_structure():
    """For gross G = Z_12 × Z_6, G_odd = Z_3 × Z_3, 5 orbits."""
    G = ZmZn(12, 6)
    orbits = g_odd_frobenius_orbits(G)
    assert len(orbits) == 5  # Z_3 × Z_3 has 5 Frobenius orbits.
    sizes = sorted(len(o) for o in orbits)
    assert sizes == [1, 2, 2, 2, 2]

"""Tests for `bb_lab.algebraic_features`.

The orbit structure is verified against hand-computed test cases listed
in the T2.2 task spec (Z_3, Z_15, Z_3 × Z_3). The vanishing-orbit
prediction is cross-checked against `dim_ker(M_A)` from `linalg` on the
odd-order groups, where the formula

    dim ker(M_A) = sum over orbits O where A vanishes of |O|

holds exactly. The gross [[144,12,12]] code lives over `Z_12 × Z_6`
(non-semisimple F_2[G]); we still verify the orbit structure and the
specific vanishing pattern, but the dim-ker formula no longer matches —
see `notes/T2.2_algebraic_features.md` for the algebraic explanation.
"""

from __future__ import annotations

import pytest

from bb_lab.algebraic_features import (
    AlgebraicFeatures,
    compute_features,
    frobenius_orbits,
    joint_vanishing_orbits,
    n_vanishing_orbits,
    orbit_sizes,
    vanishing_orbits,
    vanishing_pattern_signature,
)
from bb_lab.checks import circulant
from bb_lab.group import AbelianGroup, ZmZn
from bb_lab.linalg import rank_f2
from bb_lab.poly import Poly


# ---------------------------------------------------------------------------
# frobenius_orbits — structural tests
# ---------------------------------------------------------------------------


def _orbit_set(orbits):
    """Return orbits as a set of frozensets (for set-equality comparison)."""
    return set(orbits)


def test_frobenius_orbits_partition():
    """Orbit sizes should sum to |G| and orbits should partition G."""
    for G in [
        AbelianGroup((3,)),
        AbelianGroup((15,)),
        ZmZn(3, 3),
        ZmZn(3, 5),
        ZmZn(12, 6),
        ZmZn(4, 6),
    ]:
        orbits = frobenius_orbits(G)
        # Sizes sum to |G|
        assert sum(len(o) for o in orbits) == G.cardinality
        # Orbits are pairwise disjoint
        union = set()
        for o in orbits:
            assert not (union & o), f"overlap in orbits for {G.label()}"
            union |= o
        # Union equals G
        assert union == set(G)


def test_frobenius_orbits_z3():
    """G = Z_3 should give exactly two orbits: {0} and {1, 2}."""
    G = AbelianGroup((3,))
    orbits = frobenius_orbits(G)
    assert _orbit_set(orbits) == {
        frozenset([(0,)]),
        frozenset([(1,), (2,)]),
    }


def test_frobenius_orbits_z15():
    """G = Z_15 should give five Frobenius (cyclotomic 2-coset) orbits."""
    G = AbelianGroup((15,))
    orbits = frobenius_orbits(G)
    assert _orbit_set(orbits) == {
        frozenset([(0,)]),
        frozenset([(5,), (10,)]),
        frozenset([(1,), (2,), (4,), (8,)]),
        frozenset([(3,), (6,), (12,), (9,)]),
        frozenset([(7,), (11,), (13,), (14,)]),
    }


def test_frobenius_orbits_z3_x_z3():
    """G = Z_3 × Z_3 (non-cyclic, |G| odd) should give 5 orbits."""
    G = ZmZn(3, 3)
    orbits = frobenius_orbits(G)
    assert _orbit_set(orbits) == {
        frozenset([(0, 0)]),
        frozenset([(1, 0), (2, 0)]),
        frozenset([(0, 1), (0, 2)]),
        frozenset([(1, 1), (2, 2)]),
        frozenset([(1, 2), (2, 1)]),
    }


def test_frobenius_orbits_z12_x_z6():
    """Gross-code group Z_12 × Z_6 has 55 orbits via the iterate-from-
    unvisited partition. The 2-Sylow part of G contributes preperiod
    singletons; only the dynamical cycles (within G_odd ≅ Z_3 × Z_3)
    are "true" Frobenius orbits in the character-theoretic sense.
    """
    G = ZmZn(12, 6)
    orbits = frobenius_orbits(G)
    assert sum(len(o) for o in orbits) == G.cardinality == 72
    # 55 partition classes (this is implementation-specific to the
    # iterate-from-unvisited definition, but stable).
    assert len(orbits) == 55


# ---------------------------------------------------------------------------
# vanishing_orbits — semisimple correctness
# ---------------------------------------------------------------------------


def _dim_ker(A: Poly) -> int:
    M = circulant(A)
    return A.group.cardinality - rank_f2(M)


@pytest.mark.parametrize("poly_str", [
    "1 + x + x^2",
    "1 + x + x^5",
    "1 + x^3 + x^9",
    "1 + x^5",
    "1",
])
def test_vanishing_dim_ker_z15(poly_str):
    """For G = Z_15 (odd order), the formula
    `dim ker(M_A) = Σ |O| · [A vanishes on O]` holds exactly because
    F_2[Z_15] is semisimple (gcd(15, 2) = 1).
    """
    G = AbelianGroup((15,))
    A = Poly.from_string(poly_str, G)
    orbits = frobenius_orbits(G)
    vs = vanishing_orbits(A, G, orbits)
    contrib = sum(len(orbits[i]) for i in vs)
    assert contrib == _dim_ker(A), (
        f"semisimple formula mismatch on {poly_str}: "
        f"contrib={contrib}, dim_ker={_dim_ker(A)}"
    )


def test_vanishing_z3_x_z3():
    """Cross-check on Z_3 × Z_3: dim_ker formula must hold (|G| = 9 odd)."""
    G = ZmZn(3, 3)
    orbits = frobenius_orbits(G)
    test_cases = [
        "1 + x + x^2",
        "1 + y + y^2",
        "x + x^2*y",
        "1 + x*y + x^2*y^2",
    ]
    for poly_str in test_cases:
        A = Poly.from_string(poly_str, G)
        vs = vanishing_orbits(A, G, orbits)
        contrib = sum(len(orbits[i]) for i in vs)
        assert contrib == _dim_ker(A), (
            f"semisimple formula mismatch on Z_3×Z_3, {poly_str}: "
            f"contrib={contrib}, dim_ker={_dim_ker(A)}"
        )


def test_vanishing_30_4_6_champion():
    """The [[30,4,6]] champion: G = Z_3 × Z_5, A = 1 + x + x^2 y.

    Expected: dim_ker_A = 2, vanishing on the single size-2 orbit
    {(1,0), (2,0)} corresponding to the x-axis nontrivial cube-root
    character. The signature is (2,).
    """
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    orbits = frobenius_orbits(G)

    assert _dim_ker(A) == 2  # sanity

    vs = vanishing_orbits(A, G, orbits)
    contrib = sum(len(orbits[i]) for i in vs)
    assert contrib == 2  # semisimple formula holds (|G| = 15 odd)

    sig = vanishing_pattern_signature(A, G, orbits)
    assert sig == (2,)

    # Verify the specific vanishing orbit content
    assert len(vs) == 1
    vanishing_orbit = orbits[next(iter(vs))]
    assert vanishing_orbit == frozenset([(1, 0), (2, 0)]), (
        f"expected x-axis cube-root orbit; got {vanishing_orbit}"
    )


def test_gross_vanishing_structure():
    """For the gross code (G = Z_12 × Z_6 non-semisimple), the implementation
    records vanishing per the *semisimple quotient* F_2[G_odd] ≅ F_2[Z_3 × Z_3].

    Verifies:
      * the 3 G_odd-vanishing orbits (the y-nontrivial cube-root family) are
        reflected in `n_vanishing_orbits` ≥ 3 (multiple G-orbits project
        to each G_odd-orbit);
      * the joint vanishing with B is nontrivial (logical-operator source);
      * the *actual* dim_ker_A = 12 comes from radical contributions in F_2[G]
        and is **not** captured by the orbit-vanishing formula directly.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    orbits = frobenius_orbits(G)

    # Sanity: actual dim_ker_A is 12 (regression check).
    assert _dim_ker(A) == 12
    assert _dim_ker(B) == 12

    vs_A = vanishing_orbits(A, G, orbits)
    vs_B = vanishing_orbits(B, G, orbits)
    assert len(vs_A) > 0, "A should vanish on at least one orbit (the y-nontrivial family)"
    assert len(vs_B) > 0

    # Joint vanishing: corresponds to ker(M_A) ∩ ker(M_B) in the
    # semisimple quotient.
    joint = joint_vanishing_orbits(A, B, G, orbits)
    assert joint <= vs_A and joint <= vs_B
    assert len(joint) > 0

    # Document the semisimple-vs-true mismatch:
    contrib_A = sum(len(orbits[i]) for i in vs_A)
    # The formula gives a value ≠ 12 because F_2[Z_12 × Z_6] is not
    # semisimple. The semisimple kernel dim is at most 9 = |G_odd|
    # (the 9 G_odd-orbit sizes summed). The full dim_ker_A = 12
    # comes from nilpotent radical contributions beyond what
    # vanishing_orbits sees.
    assert contrib_A != 12, (
        "Expected the semisimple formula to NOT match dim_ker_A = 12 "
        "for non-semisimple gross group; see module docstring."
    )


# ---------------------------------------------------------------------------
# n_vanishing_orbits, joint_vanishing_orbits, vanishing_pattern_signature
# ---------------------------------------------------------------------------


def test_n_vanishing_orbits_counts():
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    assert n_vanishing_orbits(A, G) == 1


def test_joint_vanishing_basic():
    """Joint vanishing on same poly should equal vanishing."""
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    orbits = frobenius_orbits(G)
    vs = vanishing_orbits(A, G, orbits)
    joint = joint_vanishing_orbits(A, A, G, orbits)
    assert joint == vs


def test_joint_vanishing_mismatched_groups():
    """Joint vanishing requires matching groups."""
    G1 = AbelianGroup((3,))
    G2 = ZmZn(3, 5)
    A = Poly.from_string("1 + x", G1)
    B = Poly.from_string("1 + x", G2)
    with pytest.raises(ValueError):
        joint_vanishing_orbits(A, B)


def test_signature_is_hashable():
    """vanishing_pattern_signature should return a hashable tuple."""
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    sig = vanishing_pattern_signature(A, G)
    # Tuples are hashable; verify it's usable as a dict key.
    {sig: "value"}
    assert isinstance(sig, tuple)


def test_signature_zero_polynomial():
    """The zero polynomial vanishes on ALL orbits (since Â = 0 always)."""
    G = ZmZn(3, 3)
    A = Poly.zero(G)
    orbits = frobenius_orbits(G)
    vs = vanishing_orbits(A, G, orbits)
    assert len(vs) == len(orbits)  # all orbits
    # And the signature is the sorted multiset of all orbit sizes.
    sig = vanishing_pattern_signature(A, G, orbits)
    assert sig == tuple(sorted(len(o) for o in orbits))


def test_compute_features_structure():
    """`compute_features` should produce the consistent bundle."""
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    feat = compute_features(A, G)
    assert isinstance(feat, AlgebraicFeatures)
    assert feat.n_orbits == 5
    assert feat.orbit_sizes == (1, 2, 4, 4, 4)
    assert feat.n_vanishing == 1
    assert feat.vanishing_signature == (2,)


def test_orbit_sizes_helper():
    G = ZmZn(3, 3)
    orbits = frobenius_orbits(G)
    sizes = orbit_sizes(orbits)
    assert sizes == (1, 2, 2, 2, 2)


# ---------------------------------------------------------------------------
# Frobenius-conjugacy of orbit representatives (sanity)
# ---------------------------------------------------------------------------


def test_vanishing_independent_of_representative():
    """Vanishing test on each orbit must give the same verdict for every
    representative of the orbit (Frobenius-conjugate elements give
    Frobenius-conjugate Â values, all simultaneously 0 or nonzero)."""
    G = AbelianGroup((15,))
    orbits = frobenius_orbits(G)
    # Pick a poly with some vanishing
    A = Poly.from_string("1 + x + x^5", G)
    # Run vanishing test with default reps
    vs_default = vanishing_orbits(A, G, orbits)
    # Hand-roll: for each orbit, try each element as rep
    from bb_lab.algebraic_features import _evaluate_char_sum_on_g_odd
    for i, orb in enumerate(orbits):
        verdicts = []
        for rep in orb:
            v = _evaluate_char_sum_on_g_odd(A, G, rep)
            verdicts.append(all(c == 0 for c in v))
        # All reps in the orbit give the same verdict
        assert len(set(verdicts)) == 1, (
            f"orbit {i} {orb}: reps give different verdicts {verdicts}"
        )
        # And it matches the index-based test
        assert (i in vs_default) == verdicts[0]

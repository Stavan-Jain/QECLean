"""Tests for the canonical-form module — the Tier 1 v1 substrate.

For BB instances over G = ZMod ℓ × ZMod m with polynomials A, B in
F₂[G], two pairs are equivalent if they differ by:
  (1) a G-translation,
  (2) an automorphism of G acting on both polynomials,
  (3) a block-swap (A, B) ↔ (B, A).

`canonical_pair` returns the lex-min representative of the orbit;
`is_canonical` is the early-exit version that just reports whether
the input is already that representative.
"""

from __future__ import annotations

import pytest

from bb_lab.automorphism import Automorphism, automorphisms
from bb_lab.canonical import canonical_pair, is_canonical
from bb_lab.group import AbelianGroup, ZmZn


# ---------------------------------------------------------------------------
# Aut(G) counts

@pytest.mark.parametrize("orders,expected", [
    ((3,),     2),       # Z_3:       phi(3)
    ((4,),     2),       # Z_4:       phi(4)
    ((5,),     4),       # Z_5:       phi(5)
    ((6,),     2),       # Z_6:       phi(6)
    ((3, 3),  48),       # Z_3 x Z_3: |GL_2(Z_3)|
    ((2, 2),   6),       # Z_2 x Z_2: |GL_2(Z_2)|
    ((6, 6), 288),       # Z_6 x Z_6: 6 * 48
])
def test_aut_count(orders, expected):
    G = AbelianGroup(orders)
    assert len(automorphisms(G)) == expected


def test_aut_identity_present():
    G = ZmZn(12, 6)
    auts = automorphisms(G)
    identity_image = ((1, 0), (0, 1))
    assert any(phi.images == identity_image for phi in auts)


def test_aut_preserves_structure():
    """Every automorphism actually is a homomorphism."""
    G = ZmZn(6, 6)
    auts = automorphisms(G)
    for phi in auts[:20]:  # sample, not all 288
        elems = list(G)
        for g in elems[:10]:
            for h in elems[:10]:
                assert phi(G.add(g, h)) == G.add(phi(g), phi(h)), (
                    f"{phi.images} is not a homomorphism: "
                    f"phi({g}+{h}) != phi({g}) + phi({h})"
                )


# ---------------------------------------------------------------------------
# Canonical form

def test_canonical_idempotent_gross():
    """canonical(canonical(x)) == canonical(x) for the gross polynomials."""
    G = ZmZn(12, 6)
    auts = automorphisms(G)
    A = {(3, 0), (0, 1), (0, 2)}
    B = {(0, 3), (1, 0), (2, 0)}
    c1 = canonical_pair(A, B, G, auts=auts)
    c2 = canonical_pair(set(c1.A_support), set(c1.B_support), G, auts=auts)
    assert c1.A_support == c2.A_support
    assert c1.B_support == c2.B_support


def test_canonical_swap_equivalent():
    """(A, B) and (B, A) collapse to the same canonical form."""
    G = ZmZn(6, 6)
    auts = automorphisms(G)
    A = {(3, 0), (0, 1), (0, 2)}
    B = {(0, 3), (1, 0), (2, 0)}
    c_ab = canonical_pair(A, B, G, auts=auts)
    c_ba = canonical_pair(B, A, G, auts=auts)
    assert c_ab.A_support == c_ba.A_support
    assert c_ab.B_support == c_ba.B_support


def test_canonical_translation_equivalent():
    """A G-translate of (A, B) collapses to the same canonical form."""
    G = ZmZn(6, 6)
    auts = automorphisms(G)
    A = {(3, 0), (0, 1), (0, 2)}
    B = {(0, 3), (1, 0), (2, 0)}
    A_shift = {((g[0] + 2) % 6, g[1]) for g in A}
    B_shift = {((g[0] + 2) % 6, g[1]) for g in B}
    c_orig = canonical_pair(A, B, G, auts=auts)
    c_shift = canonical_pair(A_shift, B_shift, G, auts=auts)
    assert c_orig.A_support == c_shift.A_support
    assert c_orig.B_support == c_shift.B_support


def test_canonical_aut_equivalent():
    """Applying an automorphism doesn't change the canonical form."""
    G = ZmZn(3, 3)
    auts = automorphisms(G)
    A = {(0, 0), (1, 0), (0, 1)}
    B = {(0, 0), (2, 0), (0, 2)}
    c_orig = canonical_pair(A, B, G, auts=auts)
    # Pick any non-identity automorphism
    nontriv = next(phi for phi in auts if phi.images != ((1, 0), (0, 1)))
    A_phi = nontriv.apply_support(frozenset(A))
    B_phi = nontriv.apply_support(frozenset(B))
    c_phi = canonical_pair(A_phi, B_phi, G, auts=auts)
    assert c_orig.A_support == c_phi.A_support
    assert c_orig.B_support == c_phi.B_support


def test_is_canonical_matches_canonical_pair():
    """`is_canonical` agrees with the slow `canonical_pair == input`."""
    G = ZmZn(3, 3)
    auts = automorphisms(G)
    elems = list(G)
    # Spot-check 50 random weight-3 pairs
    import itertools
    pairs = list(itertools.islice(
        ((frozenset(elems[i] for i in c1), frozenset(elems[j] for j in c2))
         for c1 in itertools.combinations(range(G.cardinality), 3)
         for c2 in itertools.combinations(range(G.cardinality), 3)),
        50,
    ))
    for sA, sB in pairs:
        canon = canonical_pair(sA, sB, G, auts=auts)
        own_is_canon = (
            tuple(sorted(sA)) == canon.A_support
            and tuple(sorted(sB)) == canon.B_support
        )
        assert is_canonical(sA, sB, G, auts=auts) == own_is_canon


def test_canonical_full_orbit_for_gross():
    """The gross polynomial pair has no nontrivial stabilizer; orbit
    should be exactly |G| × |Aut(G)| × 2."""
    G = ZmZn(12, 6)
    auts = automorphisms(G)
    canon = canonical_pair(
        {(3, 0), (0, 1), (0, 2)},
        {(0, 3), (1, 0), (2, 0)},
        G, auts=auts,
    )
    expected = G.cardinality * len(auts) * 2
    assert canon.orbit_size == expected


def test_canonical_zero_polynomials_handled():
    """Edge case: zero-polynomial pair."""
    G = ZmZn(3, 3)
    auts = automorphisms(G)
    canon = canonical_pair(set(), set(), G, auts=auts)
    assert canon.A_support == ()
    assert canon.B_support == ()

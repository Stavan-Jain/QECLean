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
from bb_lab.canonical import (
    _bits_to_support,
    _support_to_bits,
    build_perm_table,
    canonical_bits,
    canonical_pair,
    is_canonical,
    is_canonical_bits,
)
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


# ---------------------------------------------------------------------------
# Bitset-level API (introduced when canonical form was migrated off
# frozenset[tuple] supports for speed)

def test_support_bits_roundtrip():
    """`_support_to_bits` then `_bits_to_support` is the identity (modulo
    set vs sorted-tuple)."""
    G = ZmZn(6, 6)
    supp = frozenset({(0, 0), (3, 0), (1, 1), (5, 4)})
    bits = _support_to_bits(supp, G)
    recovered = _bits_to_support(bits, G)
    assert set(recovered) == supp


def test_perm_table_matches_explicit_transformation():
    """For each (φ, h) entry of `build_perm_table(G)`, applying it to a
    bitset of a support coincides with applying φ then translation to
    the support directly."""
    G = ZmZn(3, 4)
    auts = automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    supp = frozenset({(0, 0), (1, 0), (2, 3)})
    bits = _support_to_bits(supp, G)
    elems = list(G)
    k = 0
    for phi in auts:
        for h in elems:
            sigma = perms[k]
            k += 1
            # Apply via the precomputed permutation.
            from bb_lab.canonical import _permute_bits
            via_perm = _permute_bits(bits, sigma)
            # Apply via the explicit phi-then-translate.
            via_explicit = _support_to_bits(
                frozenset(G.add(phi(g), h) for g in supp), G,
            )
            assert via_perm == via_explicit, (
                f"perm {k-1} (phi={phi.images}, h={h}) "
                f"disagrees with explicit transformation"
            )


def test_is_canonical_bits_agrees_with_canonical_bits():
    """For random pairs: is_canonical_bits returns True iff
    canonical_bits returns the input."""
    import itertools
    G = ZmZn(3, 3)
    perms = build_perm_table(G)
    N = G.cardinality
    pairs = list(itertools.islice(
        itertools.product(
            itertools.combinations(range(N), 3),
            itertools.combinations(range(N), 3),
        ),
        80,
    ))
    for cA, cB in pairs:
        A_bits = 0
        for i in cA: A_bits |= 1 << i
        B_bits = 0
        for j in cB: B_bits |= 1 << j
        fast = is_canonical_bits(A_bits, B_bits, perms)
        can_A, can_B, _ = canonical_bits(A_bits, B_bits, perms)
        slow = (can_A == A_bits) and (can_B == B_bits)
        assert fast == slow, (
            f"is_canonical_bits={fast} disagrees with canonical_bits "
            f"({can_A}, {can_B}) on input ({A_bits}, {B_bits})"
        )


def test_canonical_bits_orbit_size_matches_canonical_pair():
    """Orbit size as computed at the bitset layer agrees with the high
    level CanonicalPair.orbit_size."""
    G = ZmZn(3, 3)
    auts = automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    elems = list(G)
    A = frozenset({elems[0], elems[1], elems[2]})
    B = frozenset({elems[3], elems[4], elems[5]})
    canon = canonical_pair(A, B, G, auts=auts)
    _, _, orbit_bits = canonical_bits(
        _support_to_bits(A, G), _support_to_bits(B, G), perms,
    )
    assert canon.orbit_size == orbit_bits


def test_canonical_pair_accepts_precomputed_perms():
    """Passing precomputed `perms` to `canonical_pair` is equivalent to
    letting it compute the table internally."""
    G = ZmZn(3, 4)
    auts = automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    A = {(0, 0), (1, 0), (2, 3)}
    B = {(0, 1), (0, 2), (1, 2)}
    c1 = canonical_pair(A, B, G, auts=auts)
    c2 = canonical_pair(A, B, G, perms=perms)
    assert c1.A_support == c2.A_support
    assert c1.B_support == c2.B_support
    assert c1.orbit_size == c2.orbit_size

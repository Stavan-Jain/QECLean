"""Canonical form for BB-code polynomial pairs (A, B) under the
equivalence

    (A, B) ~ (g·A, g·B)               (G-translation, g ∈ G)
    (A, B) ~ (φ·A, φ·B)               (group automorphism, φ ∈ Aut(G))
    (A, B) ~ (B, A)                   (block swap)

These all preserve the resulting BB code up to qubit relabeling, so
distinct codes are in bijection with orbit representatives.

**Not yet handled**: multiplication by units of F₂[G] (gauge
equivalence). The unit group of F₂[G] for non-cyclic abelian G is
involved enough that we punt for v1; the captured equivalences are
the dominant ones in the Bravyi-table census.

The canonical representative is lex-min under a deterministic bitset
encoding of the polynomial pair. Bit `i` of a polynomial's int
encoding is set iff group element `G.from_index(i)` is in the
polynomial's support. The canonical key is `(A_bits, B_bits)`
compared as a tuple of Python ints — short-circuit on `A_bits`.

The bitset representation is faster than the previous frozenset-based
implementation by ~10-100× depending on |G|: every transformation
becomes a precomputed index permutation plus O(weight) bit operations,
versus repeated frozenset rebuilds + tuple sorts on the slow path.

Note that the bitset lex order picks a *different* canonical rep
within each orbit than the previous sorted-tuple lex order. Orbit
membership is unchanged (the equivalence relation has not moved), so
orbit counts, orbit sizes, and any downstream code that only depends
on the *equivalence class* (not the specific rep) are unaffected.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .automorphism import Automorphism, automorphisms
from .group import AbelianGroup


# ---------------------------------------------------------------------------
# Bitset helpers


def _support_to_bits(
    supp: Iterable[tuple[int, ...]], G: AbelianGroup
) -> int:
    """Encode a polynomial support as an int: bit `G.index(g)` is set
    iff `g ∈ supp`."""
    bits = 0
    for g in supp:
        bits |= 1 << G.index(g)
    return bits


def _bits_to_support(bits: int, G: AbelianGroup) -> tuple[tuple[int, ...], ...]:
    """Decode a bitset back to a sorted tuple of group elements,
    in `G.index` order."""
    out: list[tuple[int, ...]] = []
    b = bits
    while b:
        lsb = b & -b
        i = lsb.bit_length() - 1
        out.append(G.from_index(i))
        b ^= lsb
    return tuple(out)


def _permute_bits(bits: int, sigma: tuple[int, ...]) -> int:
    """Apply the index permutation `sigma` to a bitset.

    `sigma[i]` is the new index of the element previously at index `i`,
    so the resulting bitset has bit `sigma[i]` set iff `bits` had bit
    `i` set.
    """
    out = 0
    while bits:
        lsb = bits & -bits
        i = lsb.bit_length() - 1
        out |= 1 << sigma[i]
        bits ^= lsb
    return out


# ---------------------------------------------------------------------------
# Precomputed equivalence table


def build_perm_table(
    G: AbelianGroup,
    auts: list[Automorphism] | None = None,
) -> tuple[tuple[int, ...], ...]:
    """Precompute the index permutation for every `(φ, h) ∈ Aut(G) × G`.

    Returns a tuple `perms` of length `|Aut(G)| · |G|`, where
    `perms[k][i]` is the new index of `G.from_index(i)` after the
    `k`-th transformation in row-major `(φ, h)` order. Swap is handled
    separately by the canonical-form callers (it acts between the two
    polynomials, not on group indices).
    """
    if auts is None:
        auts = automorphisms(G)
    N = G.cardinality
    perms: list[tuple[int, ...]] = []
    # Precompute φ's action on each index, for each automorphism.
    elems = [G.from_index(i) for i in range(N)]
    phi_action_per_aut: list[list[int]] = []
    for phi in auts:
        phi_action_per_aut.append([G.index(phi(elems[i])) for i in range(N)])
    # For each (φ, h): σ(i) = G.index(φ(elems[i]) + h)
    for phi_action in phi_action_per_aut:
        for h in G:
            sigma = tuple(
                G.index(G.add(elems[phi_action[i]], h)) for i in range(N)
            )
            perms.append(sigma)
    return tuple(perms)


# ---------------------------------------------------------------------------
# Bitset-level public API


def is_canonical_bits(
    A_bits: int, B_bits: int, perms: tuple[tuple[int, ...], ...]
) -> bool:
    """Return True iff `(A_bits, B_bits)` is the lex-min orbit
    representative under the equivalence relation encoded by `perms`
    plus block-swap.

    Early-exits on the first transformation producing a smaller key.
    The lex-on-`(int, int)` order is reproduced by hand without tuple
    allocation, which is ~2× faster than `(tA, tB) < own_tuple` in
    the hot loop.
    """
    own_A = A_bits
    own_B = B_bits
    for sigma in perms:
        # Inline _permute_bits for A.
        tA = 0
        b = A_bits
        while b:
            lsb = b & -b
            tA |= 1 << sigma[lsb.bit_length() - 1]
            b ^= lsb
        if tA < own_A:
            return False
        tA_eq = (tA == own_A)
        # Inline _permute_bits for B (needed for the swap orientation
        # even when tA > own_A).
        tB = 0
        b = B_bits
        while b:
            lsb = b & -b
            tB |= 1 << sigma[lsb.bit_length() - 1]
            b ^= lsb
        if tA_eq and tB < own_B:
            return False
        # Swap orientation: (tB, tA) vs (own_A, own_B).
        if tB < own_A:
            return False
        if tB == own_A and tA < own_B:
            return False
    return True


def canonical_bits(
    A_bits: int, B_bits: int, perms: tuple[tuple[int, ...], ...]
) -> tuple[int, int, int]:
    """Return `(canonical_A_bits, canonical_B_bits, orbit_size)`.

    `orbit_size` counts the number of *distinct* (bits_A, bits_B)
    pairs reachable from the input under `perms × {swap?}`.
    """
    best_A = A_bits
    best_B = B_bits
    seen: set[tuple[int, int]] = set()
    seen_add = seen.add  # micro-optimization for the hot loop
    for sigma in perms:
        tA = 0
        b = A_bits
        while b:
            lsb = b & -b
            tA |= 1 << sigma[lsb.bit_length() - 1]
            b ^= lsb
        tB = 0
        b = B_bits
        while b:
            lsb = b & -b
            tB |= 1 << sigma[lsb.bit_length() - 1]
            b ^= lsb
        seen_add((tA, tB))
        seen_add((tB, tA))
        # Update lex-min over (tA, tB) and (tB, tA) candidates without
        # tuple allocation per candidate.
        if tA < best_A or (tA == best_A and tB < best_B):
            best_A = tA
            best_B = tB
        if tB < best_A or (tB == best_A and tA < best_B):
            best_A = tB
            best_B = tA
    return (best_A, best_B, len(seen))


# ---------------------------------------------------------------------------
# Group-element-level API (back-compat with the previous frozenset version)


@dataclass(frozen=True, slots=True)
class CanonicalPair:
    """Canonical orbit representative of a BB instance (A, B)."""

    group: AbelianGroup
    A_support: tuple[tuple[int, ...], ...]
    B_support: tuple[tuple[int, ...], ...]
    orbit_size: int

    @property
    def key(self) -> tuple[int, ...]:
        """Hashable canonical key used for dedup across an enumeration."""
        return (
            self.group.orders,
            self.A_support,
            self.B_support,
        )


def canonical_pair(
    A_support: frozenset[tuple[int, ...]] | set[tuple[int, ...]],
    B_support: frozenset[tuple[int, ...]] | set[tuple[int, ...]],
    G: AbelianGroup,
    *,
    auts: list[Automorphism] | None = None,
    perms: tuple[tuple[int, ...], ...] | None = None,
) -> CanonicalPair:
    """Compute the canonical representative of (A_support, B_support).

    `auts` is the Aut(G) list (passed in so the caller can cache it
    across many calls). `perms` is the precomputed permutation table
    (`build_perm_table(G, auts)`); pass it in to avoid recomputing on
    hot loops.
    """
    if perms is None:
        perms = build_perm_table(G, auts=auts)
    A_bits = _support_to_bits(A_support, G)
    B_bits = _support_to_bits(B_support, G)
    can_A, can_B, orbit_size = canonical_bits(A_bits, B_bits, perms)
    return CanonicalPair(
        group=G,
        A_support=_bits_to_support(can_A, G),
        B_support=_bits_to_support(can_B, G),
        orbit_size=orbit_size,
    )


def is_canonical(
    A_support: frozenset[tuple[int, ...]] | set[tuple[int, ...]],
    B_support: frozenset[tuple[int, ...]] | set[tuple[int, ...]],
    G: AbelianGroup,
    *,
    auts: list[Automorphism] | None = None,
    perms: tuple[tuple[int, ...], ...] | None = None,
) -> bool:
    """Fast check: is `(A_support, B_support)` already the canonical
    representative of its orbit?

    Returns True iff no transformation in `G × Aut(G) × ⟨swap⟩`
    produces a *strictly* smaller bitset key. Early-terminates the
    moment a smaller key is found.
    """
    if perms is None:
        perms = build_perm_table(G, auts=auts)
    A_bits = _support_to_bits(A_support, G)
    B_bits = _support_to_bits(B_support, G)
    return is_canonical_bits(A_bits, B_bits, perms)

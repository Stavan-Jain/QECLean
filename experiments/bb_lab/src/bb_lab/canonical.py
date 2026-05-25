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

The canonical representative is lex-min under a deterministic encoding
of the polynomial pair as a tuple of integer indices.
"""

from __future__ import annotations

from dataclasses import dataclass

from .automorphism import Automorphism, automorphisms
from .group import AbelianGroup


def _encode(supp: frozenset[tuple[int, ...]], G: AbelianGroup) -> tuple[int, ...]:
    """Sortable encoding of a polynomial via the group's row-major index."""
    return tuple(sorted(G.index(g) for g in supp))


def _pair_key(
    sA: frozenset[tuple[int, ...]], sB: frozenset[tuple[int, ...]], G: AbelianGroup
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    return (_encode(sA, G), _encode(sB, G))


def _translate(
    supp: frozenset[tuple[int, ...]], h: tuple[int, ...], G: AbelianGroup
) -> frozenset[tuple[int, ...]]:
    return frozenset(G.add(g, h) for g in supp)


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
) -> CanonicalPair:
    """Compute the canonical representative of (A_support, B_support).

    `auts` is the Aut(G) list (passed in so the caller can cache it
    across many calls).
    """
    sA = frozenset(A_support)
    sB = frozenset(B_support)
    auts = auts if auts is not None else automorphisms(G)

    # Try every (translation, automorphism, swap?) and keep the lex-min
    # pair-key. We also track orbit size by counting distinct images.
    seen_keys: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    best_key: tuple[tuple[int, ...], tuple[int, ...]] | None = None
    best_pair: tuple[
        frozenset[tuple[int, ...]], frozenset[tuple[int, ...]]
    ] | None = None

    for phi in auts:
        # Apply phi first, then translation. (Equivalent orbit since
        # the group of equivalences is a semidirect product.)
        phiA = phi.apply_support(sA)
        phiB = phi.apply_support(sB)
        for h in G:
            tA = _translate(phiA, h, G)
            tB = _translate(phiB, h, G)
            for sa, sb in ((tA, tB), (tB, tA)):
                k = _pair_key(sa, sb, G)
                seen_keys.add(k)
                if best_key is None or k < best_key:
                    best_key = k
                    best_pair = (sa, sb)

    assert best_pair is not None
    return CanonicalPair(
        group=G,
        A_support=tuple(sorted(best_pair[0])),
        B_support=tuple(sorted(best_pair[1])),
        orbit_size=len(seen_keys),
    )


def is_canonical(
    A_support: frozenset[tuple[int, ...]] | set[tuple[int, ...]],
    B_support: frozenset[tuple[int, ...]] | set[tuple[int, ...]],
    G: AbelianGroup,
    *,
    auts: list[Automorphism] | None = None,
) -> bool:
    """Fast check: is `(A_support, B_support)` already the canonical
    representative of its orbit?

    Returns True iff no transformation in `shifts × Aut(G) × ⟨swap⟩`
    produces a *strictly* smaller key. Early-terminates the moment a
    smaller key is found — typically much faster than computing the
    full canonical form, since most non-canonical pairs are eliminated
    after only a few trial transformations.
    """
    sA = frozenset(A_support)
    sB = frozenset(B_support)
    auts = auts if auts is not None else automorphisms(G)
    own_key = _pair_key(sA, sB, G)

    for phi in auts:
        phiA = phi.apply_support(sA)
        phiB = phi.apply_support(sB)
        for h in G:
            tA = _translate(phiA, h, G)
            tB = _translate(phiB, h, G)
            for sa, sb in ((tA, tB), (tB, tA)):
                k = _pair_key(sa, sb, G)
                if k < own_key:
                    return False
    return True

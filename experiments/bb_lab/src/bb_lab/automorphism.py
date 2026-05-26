"""Automorphism groups of finite abelian groups.

For Tier 1 v1 we need Aut(G) where G = ZMod n_1 × ... × ZMod n_d, in
order to mod out symmetry equivalences on BB-code polynomial pairs
(A, B) ∈ F₂[G]² before counting "distinct" codes.

A homomorphism φ: G → G is determined by where it sends the standard
generators e_i = (0, …, 1, …, 0). For φ to be well-defined,
`order(φ(e_i))` must divide `n_i`. For φ to be an isomorphism, its
image must equal G (bijective on a finite set ⇔ injective ⇔ surjective).

Strategy: brute-force enumerate all rank-d tuples of group elements
satisfying the order constraints; check each one extends to an
isomorphism by computing the image set.

For G = ZMod ℓ × ZMod m up to roughly |G| = 100, this is fast (~seconds).
For larger G we'd need the explicit GL formula on the cyclic
decomposition; defer until needed.
"""

from __future__ import annotations

from dataclasses import dataclass

from .group import AbelianGroup


@dataclass(frozen=True, slots=True)
class Automorphism:
    """A homomorphism G → G specified by where it sends each
    standard generator. The image of an arbitrary element is
    computed on demand via linearity."""

    group: AbelianGroup
    images: tuple[tuple[int, ...], ...]  # images of e_1, …, e_d

    def __call__(self, g: tuple[int, ...]) -> tuple[int, ...]:
        G = self.group
        out = tuple(0 for _ in G.orders)
        for coord, image in zip(g, self.images):
            for _ in range(coord):
                out = G.add(out, image)
        return out

    def apply_support(
        self, support: frozenset[tuple[int, ...]]
    ) -> frozenset[tuple[int, ...]]:
        return frozenset(self(g) for g in support)


def _order_divides(g: tuple[int, ...], n: int, G: AbelianGroup) -> bool:
    """`n · g == 0` in G."""
    acc = tuple(0 for _ in G.orders)
    for _ in range(n):
        acc = G.add(acc, g)
    return all(c == 0 for c in acc)


def automorphisms(G: AbelianGroup) -> list[Automorphism]:
    """Enumerate Aut(G) by brute-force generator search.

    Cost: at most |G|^rank candidates, each O(|G|) to check
    bijectivity → O(|G|^(rank+1)) total. For G = Z_ℓ × Z_m with
    |G| ≤ 100, runs in well under a second.
    """
    rank = G.rank
    orders = G.orders
    # For each generator e_i (axis i), candidate images are
    # elements x ∈ G with order(x) | n_i.
    candidates_per_axis: list[list[tuple[int, ...]]] = []
    for axis_i in range(rank):
        n_i = orders[axis_i]
        cands = [g for g in G if _order_divides(g, n_i, G)]
        candidates_per_axis.append(cands)

    auts: list[Automorphism] = []
    n = G.cardinality

    def _recurse(prefix: list[tuple[int, ...]]) -> None:
        axis = len(prefix)
        if axis == rank:
            phi = Automorphism(group=G, images=tuple(prefix))
            # Bijectivity: image set has |G| elements.
            seen = set()
            for g in G:
                seen.add(phi(g))
                if len(seen) > n:
                    break
            if len(seen) == n:
                auts.append(phi)
            return
        for c in candidates_per_axis[axis]:
            prefix.append(c)
            _recurse(prefix)
            prefix.pop()

    _recurse([])
    return auts

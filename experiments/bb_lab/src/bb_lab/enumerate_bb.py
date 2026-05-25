"""Weight-bounded enumeration of canonical BB-code polynomial pairs.

For a finite abelian group G and a weight bound `weight`, enumerate
all distinct (modulo `canonical.canonical_pair`) BB instances with
`weight(A) = weight(B) = weight` and produces:
  - canonical (A, B) supports
  - n, k
  - polynomial weights
  - rank H_X, rank H_Z, dim ker A, dim ker B

`itertools.combinations` is the inner loop; the canonical-form check
uses the bitset fast path (`is_canonical_bits` against a precomputed
`(φ, h)` permutation table). Pairs are skipped early if their bitset
key is dominated by any transformation — most pairs early-exit after
a handful of permutation applications.

For G = Z_3 × Z_3 (|G|=9, |Aut|=48), weight 3 enumeration is
nearly instant. For G = Z_6 × Z_6 (|G|=36, |Aut|=288), weight 3 fits
in minutes. For G = Z_12 × Z_6 (the gross group), weight 3 takes
hours; that's the asymptote we expect from a "canonical-A then
canonical-B" split, deferred to a future move.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Iterator

from .automorphism import automorphisms
from .canonical import (
    CanonicalPair,
    build_perm_table,
    canonical_bits,
    is_canonical_bits,
    _bits_to_support,
)
from .checks import bb_check_matrices, circulant
from .codeparams import code_params
from .group import AbelianGroup
from .linalg import rank_f2
from .poly import Poly


@dataclass(frozen=True, slots=True)
class EnumeratedInstance:
    """A canonical BB instance + cheap (L0) features."""

    canonical: CanonicalPair
    n: int
    k: int
    A_weight: int
    B_weight: int
    rank_HX: int
    rank_HZ: int
    dim_ker_A: int
    dim_ker_B: int


def _to_poly(
    supp: tuple[tuple[int, ...], ...], G: AbelianGroup
) -> Poly:
    return Poly(support=frozenset(supp), group=G)


def _make_instance(canon: CanonicalPair) -> EnumeratedInstance:
    G = canon.group
    A = _to_poly(canon.A_support, G)
    B = _to_poly(canon.B_support, G)
    checks = bb_check_matrices(A, B)
    params = code_params(checks)
    dim_ker_A = G.cardinality - rank_f2(circulant(A))
    dim_ker_B = G.cardinality - rank_f2(circulant(B))
    return EnumeratedInstance(
        canonical=canon,
        n=params.n,
        k=params.k,
        A_weight=len(canon.A_support),
        B_weight=len(canon.B_support),
        rank_HX=params.rank_HX,
        rank_HZ=params.rank_HZ,
        dim_ker_A=dim_ker_A,
        dim_ker_B=dim_ker_B,
    )


def enumerate_canonical_pairs(
    G: AbelianGroup,
    *,
    weight: int,
    only_k_geq: int | None = None,
    verbose: bool = False,
) -> Iterator[EnumeratedInstance]:
    """Yield canonical BB instances with `weight(A) = weight(B) = weight`.

    `only_k_geq`: if set, drop instances with k < this value (k=0 codes
    have no logicals; not interesting for distance work).
    """
    auts = automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    N = G.cardinality
    if verbose:
        from sys import stderr
        print(
            f"enumerate: |G|={N}, |Aut(G)|={len(auts)}, "
            f"weight={weight}, "
            f"choose(|G|, w)={_binom(N, weight)} polys, "
            f"choose(|G|, w)^2={_binom(N, weight)**2} raw pairs, "
            f"|perms|={len(perms)}",
            file=stderr,
        )

    # Walk raw pairs in lex order of their bitsets. Combinations come
    # from itertools, so the bitset for `combo` is just `sum(1<<i for i
    # in combo)`. Use `is_canonical_bits` for the early-exit check; only
    # the surviving canonical reps incur the full canonical_bits walk
    # (needed for the orbit-size count).
    for combo_A in itertools.combinations(range(N), weight):
        A_bits = 0
        for i in combo_A:
            A_bits |= 1 << i
        for combo_B in itertools.combinations(range(N), weight):
            B_bits = 0
            for j in combo_B:
                B_bits |= 1 << j
            if not is_canonical_bits(A_bits, B_bits, perms):
                continue
            # Surviving pairs are canonical; compute orbit size and
            # repackage as group-element tuples.
            can_A, can_B, orbit_size = canonical_bits(A_bits, B_bits, perms)
            # `is_canonical_bits` already guaranteed `(A_bits, B_bits)`
            # is the lex-min rep, so `can_A == A_bits` and `can_B == B_bits`.
            assert (can_A, can_B) == (A_bits, B_bits), (
                "canonical_bits disagrees with is_canonical_bits — bug"
            )
            canon = CanonicalPair(
                group=G,
                A_support=_bits_to_support(can_A, G),
                B_support=_bits_to_support(can_B, G),
                orbit_size=orbit_size,
            )
            inst = _make_instance(canon)
            if only_k_geq is not None and inst.k < only_k_geq:
                continue
            yield inst


def _binom(n: int, k: int) -> int:
    from math import comb
    return comb(n, k)

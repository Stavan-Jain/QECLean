"""Weight-bounded enumeration of canonical BB-code polynomial pairs.

For a finite abelian group G and a weight bound `w_max`, enumerate
all distinct (modulo `canonical.canonical_pair`) BB instances with
`weight(A), weight(B) ≤ w_max` and produces:
  - canonical (A, B) supports
  - n, k
  - polynomial weights
  - kernel dimensions (k = 2·dim ker A ∩ ker B is already in `code_params`)

`itertools.combinations` is the inner loop; canonical-form dedup
happens via a `set` of canonical keys. We additionally skip pairs
where either polynomial is zero (those are degenerate).

For G = Z_3 × Z_3 (|G|=9, |Aut|=48), weight 3 enumeration is
nearly instant. For G = Z_6 × Z_6 (|G|=36, |Aut|=288), weight 3 is
still O(seconds). Beyond that we'd need smarter enumeration (canonical
A first, then canonical-B-given-A); deferred.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Iterator

import numpy as np

from .automorphism import automorphisms
from .canonical import CanonicalPair, canonical_pair
from .checks import bb_check_matrices
from .codeparams import code_params
from .group import AbelianGroup
from .linalg import nullspace_f2, rank_f2
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


def _to_poly(supp: tuple[tuple[int, ...], ...], G: AbelianGroup) -> Poly:
    return Poly(support=frozenset(supp), group=G)


def _make_instance(
    canon: CanonicalPair,
) -> EnumeratedInstance:
    G = canon.group
    A = _to_poly(canon.A_support, G)
    B = _to_poly(canon.B_support, G)
    checks = bb_check_matrices(A, B)
    params = code_params(checks)
    # Kernel dims for each individual polynomial
    from .checks import circulant
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
    elems = list(G)
    if verbose:
        from sys import stderr
        print(
            f"enumerate: |G|={G.cardinality}, |Aut(G)|={len(auts)}, "
            f"weight={weight}, "
            f"choose(|G|, w)={_binom(G.cardinality, weight)} polys, "
            f"choose(|G|, w)^2={_binom(G.cardinality, weight)**2} pairs",
            file=stderr,
        )
    # Fast-path strategy: walk raw pairs in lex order. For each, check
    # `is_canonical` (early-exits on the first smaller orbit element).
    # We yield only pairs that are themselves the canonical rep — no
    # set-of-canonical-keys needed, since each canonical rep is visited
    # exactly once.
    from .canonical import is_canonical
    for poly_A_idx in itertools.combinations(range(G.cardinality), weight):
        sA = frozenset(elems[i] for i in poly_A_idx)
        for poly_B_idx in itertools.combinations(range(G.cardinality), weight):
            sB = frozenset(elems[i] for i in poly_B_idx)
            if not is_canonical(sA, sB, G, auts=auts):
                continue
            # Compute full canonical form (just for orbit-size — the
            # representative is already sA, sB).
            canon = canonical_pair(sA, sB, G, auts=auts)
            inst = _make_instance(canon)
            if only_k_geq is not None and inst.k < only_k_geq:
                continue
            yield inst


def _binom(n: int, k: int) -> int:
    from math import comb
    return comb(n, k)

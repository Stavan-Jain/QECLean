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

The serial entry point is `enumerate_canonical_pairs(G, weight=…)`,
yielding `EnumeratedInstance`s lazily. For large groups (|G| ≥ 36
with weight 3) the same workload can be sharded across worker
processes via `enumerate_canonical_pairs_parallel(G, weight=…,
n_workers=N)`, which returns a list (parallel results don't stream
back as cleanly as a single iterator). The shard split is by
`combo_A_idx % n_workers`, so each worker independently calls
`is_canonical_bits` over a disjoint subset of outer combinations.
Each worker streams its EnumeratedInstance hits to a per-shard
pickle file under a TemporaryDirectory; the driver merges at the
end. Output order is non-deterministic across runs (depends on
worker scheduling) — callers needing canonical ordering should sort
by `inst.canonical.key`.

For G = Z_3 × Z_3 (|G|=9, |Aut|=48), weight 3 enumeration is
nearly instant. For G = Z_6 × Z_6 (|G|=36, |Aut|=288), weight 3 fits
in ~5–10 minutes serial; parallel-4 brings it under 2 minutes. For
G = Z_12 × Z_6 (the gross group), parallel-8 brings tens of hours
serial down to a small number of hours.
"""

from __future__ import annotations

import itertools
import multiprocessing
import os
import pickle
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
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


# ---------------------------------------------------------------------------
# Parallel enumeration
#
# The bitset canonical check is embarrassingly parallel along the outer
# `combo_A` axis. We shard by `combo_A_idx % n_workers` so each worker
# walks the entire range(N) outer combination space but only processes
# its assigned residue. This keeps the shard logic 5-line-trivial and
# load-balanced (early `combo_A`s have heavier inner work, but each
# worker gets a mix of early/late residues).
#
# Each worker streams pickled EnumeratedInstance objects to a per-shard
# file under a tmpdir; the driver merges at the end. This avoids
# accumulating the full result set in worker memory (Z_12 × Z_6 weight 3
# could plausibly have 100k+ canonical pairs).


def _enumerate_shard_worker(
    G_orders: tuple[int, ...],
    weight: int,
    perms: tuple[tuple[int, ...], ...],
    worker_id: int,
    n_workers: int,
    only_k_geq: int | None,
    out_path: str,
) -> int:
    """Worker entry: enumerate the `combo_A_idx % n_workers == worker_id`
    shard. Stream hits as pickled records to `out_path`. Return count.

    Top-level so spawn-based multiprocessing can pickle the function
    reference.
    """
    G = AbelianGroup(orders=G_orders)
    N = G.cardinality
    yielded = 0
    with open(out_path, "wb") as f:
        for combo_A_idx, combo_A in enumerate(
            itertools.combinations(range(N), weight)
        ):
            if combo_A_idx % n_workers != worker_id:
                continue
            A_bits = 0
            for i in combo_A:
                A_bits |= 1 << i
            for combo_B in itertools.combinations(range(N), weight):
                B_bits = 0
                for j in combo_B:
                    B_bits |= 1 << j
                if not is_canonical_bits(A_bits, B_bits, perms):
                    continue
                can_A, can_B, orbit_size = canonical_bits(
                    A_bits, B_bits, perms,
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
                pickle.dump(inst, f, protocol=pickle.HIGHEST_PROTOCOL)
                yielded += 1
    return yielded


def enumerate_canonical_pairs_parallel(
    G: AbelianGroup,
    *,
    weight: int,
    only_k_geq: int | None = None,
    n_workers: int | None = None,
    verbose: bool = False,
) -> list[EnumeratedInstance]:
    """Parallel variant of `enumerate_canonical_pairs`. Returns a list
    (order is *not* deterministic across runs — depends on worker
    scheduling). Use ``sorted(result, key=lambda i: i.canonical.key)``
    if you need a canonical order.

    `n_workers` defaults to `min(os.cpu_count(), 8)`, matching typical
    laptop CPU counts (more workers don't help past 8 because each one
    carries its own perms table). Set to 1 to round-trip through the
    parallel scaffolding without actually parallelising (useful for
    debug).
    """
    if n_workers is None:
        n_workers = min(os.cpu_count() or 1, 8)
    n_workers = max(int(n_workers), 1)

    auts = automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    N = G.cardinality
    if verbose:
        print(
            f"enumerate (parallel): |G|={N}, |Aut(G)|={len(auts)}, "
            f"weight={weight}, "
            f"choose(|G|, w)^2={_binom(N, weight)**2} raw pairs, "
            f"|perms|={len(perms)}, n_workers={n_workers}",
            file=sys.stderr,
        )

    # Fast path: 1 worker → no IPC needed; reuse the serial iterator.
    if n_workers == 1:
        return list(enumerate_canonical_pairs(
            G, weight=weight, only_k_geq=only_k_geq, verbose=False,
        ))

    with tempfile.TemporaryDirectory(prefix="bb_lab_enum_") as tmpdir:
        out_paths = [
            str(Path(tmpdir) / f"shard-{wid:03d}.pkl")
            for wid in range(n_workers)
        ]
        # `spawn` so worker init is hermetic (no inherited stdout
        # buffers, no copy-on-write Python state from the driver).
        ctx = multiprocessing.get_context("spawn")
        with ctx.Pool(processes=n_workers) as pool:
            tasks = [
                pool.apply_async(
                    _enumerate_shard_worker,
                    (G.orders, weight, perms, wid, n_workers, only_k_geq,
                     out_paths[wid]),
                )
                for wid in range(n_workers)
            ]
            counts = [t.get() for t in tasks]

        if verbose:
            print(
                f"  per-shard yields: {counts}  (total {sum(counts)})",
                file=sys.stderr,
            )

        results: list[EnumeratedInstance] = []
        for p in out_paths:
            try:
                with open(p, "rb") as f:
                    while True:
                        try:
                            results.append(pickle.load(f))
                        except EOFError:
                            break
            except FileNotFoundError:
                # Worker produced no hits → no file written; fine.
                continue
    return results

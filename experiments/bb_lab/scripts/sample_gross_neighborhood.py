"""Tier-1 targeted neighborhood sampling (replaces Stage 1 full enumerate).

`bb-lab enumerate --ell 3 --m 15 --weight 3` walks C(45,3)² = 201M raw
pairs and turned out to be hours of wall time even at parallel-8.
`bb-lab enumerate --ell 12 --m 6` would be worse. Instead, sample
structured *neighborhoods* of known Bravyi-style polynomial pairs by
varying one or two exponents, canonicalize via `canonical_pair`, dedupe,
and upsert.

Covered groups (the round-1 blind spots from HANDOFF_R2.md §5):

  Multi-prime mixed-rank G_odd:
    Z_3 × Z_15 (|G|=45, G_odd = Z_3² × Z_5)  ← bb_90's structural class
    Z_3 × Z_21 (|G|=63, G_odd = Z_3² × Z_7)
    Z_5 × Z_15 (|G|=75, G_odd = Z_3  × Z_5²)

  Gross-scale (no full enumeration even attempted):
    Z_12 × Z_6  (|G|=72, gross group)
    Z_12 × Z_12 (|G|=144, bb_288 group)

Total wall: ~10-15 min. Output: ~600-1000 unique canonical instances
across the five groups.

Usage:
  cd experiments/bb_lab
  uv run python scripts/sample_gross_neighborhood.py
"""

from __future__ import annotations

import itertools
import time
from pathlib import Path

from bb_lab.automorphism import automorphisms
from bb_lab.canonical import CanonicalPair, build_perm_table, canonical_pair
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.group import ZmZn
from bb_lab.linalg import rank_f2
from bb_lab.poly import Poly
from bb_lab.store import StoredInstance, canonical_hash, connect, upsert_instance

LAB_ROOT = Path(__file__).resolve().parent.parent
DB_PATH = LAB_ROOT / "data" / "bb_instances.duckdb"


def _stored_from_canon(
    canon: CanonicalPair, ell: int, m: int, code_prefix: str
) -> StoredInstance | None:
    """Build a StoredInstance from a CanonicalPair; return None if k < 2."""
    G = canon.group
    A = Poly(support=frozenset(canon.A_support), group=G)
    B = Poly(support=frozenset(canon.B_support), group=G)
    checks = bb_check_matrices(A, B)
    params = code_params(checks)
    if params.k < 2:
        return None
    dim_ker_A = G.cardinality - rank_f2(circulant(A))
    dim_ker_B = G.cardinality - rank_f2(circulant(B))
    A_poly = A.canonical_string()
    B_poly = B.canonical_string()
    iid = canonical_hash(G.label(), A_poly, B_poly)
    return StoredInstance(
        instance_id=iid,
        code_id=f"{code_prefix}_{iid[:8]}",
        group_struct=G.label(),
        ell=ell,
        m=m,
        n=params.n,
        k=params.k,
        A_poly=A_poly,
        B_poly=B_poly,
        A_weight=len(canon.A_support),
        B_weight=len(canon.B_support),
        rank_HX=params.rank_HX,
        rank_HZ=params.rank_HZ,
        dim_ker_A=dim_ker_A,
        dim_ker_B=dim_ker_B,
        orbit_size=canon.orbit_size,
    )


def _gross_perturbations(ell: int, m: int):
    """Yield raw (A_supp, B_supp) pairs around `(x^a + y^b + y^c, y^d + x^e + x^f)`,
    seeded from gross `a=3, b=1, c=2, d=3, e=1, f=2`.

    The shape "one term on the lone axis + two terms on the other axis"
    is preserved; only exponents move. Most of the explored variation
    lives in the smaller m-direction so canonicalization keeps the
    output set tractable.
    """

    def supp(*terms):
        return frozenset((a % ell, b % m) for a, b in terms)

    # Family A1: vary A's x-exponent, B fixed at (y^3, x^1, x^2).
    for a in range(ell):
        yield supp((a, 0), (0, 1), (0, 2)), supp((0, 3), (1, 0), (2, 0))

    # Family A2: vary A's y-pair (b1 < b2), B fixed.
    for b1, b2 in itertools.combinations(range(m), 2):
        yield supp((3, 0), (0, b1), (0, b2)), supp((0, 3), (1, 0), (2, 0))

    # Family B1: A fixed at gross, vary B's y-exponent.
    for d in range(m):
        yield supp((3, 0), (0, 1), (0, 2)), supp((0, d), (1, 0), (2, 0))

    # Family B2: A fixed, vary B's x-pair (e1 < e2).
    for e1, e2 in itertools.combinations(range(ell), 2):
        yield supp((3, 0), (0, 1), (0, 2)), supp((0, 3), (e1, 0), (e2, 0))

    # Family AB: vary both lone-axis exponents simultaneously.
    for a, d in itertools.product(range(ell), range(m)):
        yield supp((a, 0), (0, 1), (0, 2)), supp((0, d), (1, 0), (2, 0))


def _bb288_perturbations(ell: int, m: int):
    """Yield raw pairs around bb_288 `(x^3 + y^2 + y^7, y^3 + x + x^2)` on Z_12 × Z_12."""

    def supp(*terms):
        return frozenset((a % ell, b % m) for a, b in terms)

    # Vary A's x-exponent.
    for a in range(ell):
        yield supp((a, 0), (0, 2), (0, 7)), supp((0, 3), (1, 0), (2, 0))

    # Vary A's y-pair.
    for b1, b2 in itertools.combinations(range(m), 2):
        yield supp((3, 0), (0, b1), (0, b2)), supp((0, 3), (1, 0), (2, 0))

    # Vary B's y-exponent.
    for d in range(m):
        yield supp((3, 0), (0, 2), (0, 7)), supp((0, d), (1, 0), (2, 0))


def _bb90_perturbations(ell: int, m: int):
    """Yield raw pairs around the published bb_90 polynomials on Z_15 × Z_3.

    bb_90's published seed: `A = x^9 + y + y^2`, `B = 1 + x^2 + x^7`
    (group Z_15 × Z_3, so ell = 15, m = 3). This generator works for
    ANY (ell ≥ 15, m ≥ 3) — exponents wrap modulo. On Z_15 × Z_3
    this directly perturbs bb_90; on Z_21 × Z_3 the same shape gives
    a Z_3² × Z_7 analogue; on Z_15 × Z_5 a Z_3 × Z_5² analogue.

    Templates:
      T1. Vary A's x-exponent, B = 1 + x^2 + x^7.
      T2. Vary B's x-pair, A = x^9 + y + y^2.
      T3. Vary A's x-exp AND y-pair simultaneously.
      T4. Vary B's constant-shift (replace `1` with x^k) and x-pair.
    """

    def supp(*terms):
        return frozenset((a % ell, b % m) for a, b in terms)

    # T1: vary A's x-exponent (the long-axis lone term).
    for a in range(ell):
        yield supp((a, 0), (0, 1), (0, 2)), supp((0, 0), (2, 0), (7 % ell, 0))

    # T2: vary B's x-pair (e1, e2), keep A = x^9 + y + y^2 (or analog).
    a_seed = min(9, ell - 1)
    for e1, e2 in itertools.combinations(range(1, ell), 2):
        yield supp((a_seed, 0), (0, 1), (0, 2)), supp((0, 0), (e1, 0), (e2, 0))

    # T3: vary A's x-exp + y-pair (b1, b2).
    for a in range(ell):
        for b1, b2 in itertools.combinations(range(1, m), 2):
            yield supp((a, 0), (0, b1), (0, b2)), supp((0, 0), (2, 0), (7 % ell, 0))

    # T4: vary B's constant-shift (B = x^k + x^e1 + x^e2 — all x-axis).
    for k in range(ell):
        for e1, e2 in itertools.combinations(range(ell), 2):
            if k in (e1, e2):
                continue
            yield supp((a_seed, 0), (0, 1), (0, 2)), supp((k, 0), (e1, 0), (e2, 0))


def _multiprime_perturbations(ell: int, m: int):
    """Compatibility wrapper used by older callers; alias to bb_90-style."""
    yield from _bb90_perturbations(ell, m)


def _sample_group(ell: int, m: int, perturbations, code_prefix: str) -> int:
    """Canonicalize, dedupe, upsert. Return count of unique k≥2 instances inserted."""
    G = ZmZn(ell, m)
    auts = automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    seen_ids: set[str] = set()
    n_added = 0
    n_raw = 0
    n_k_zero = 0

    with connect(DB_PATH) as con:
        for A_supp, B_supp in perturbations(ell, m):
            n_raw += 1
            if len(A_supp) < 3 or len(B_supp) < 3:
                continue  # collision after modular reduction
            canon = canonical_pair(A_supp, B_supp, G, auts=auts, perms=perms)
            stored = _stored_from_canon(canon, ell, m, code_prefix)
            if stored is None:
                n_k_zero += 1
                continue
            if stored.instance_id in seen_ids:
                continue
            seen_ids.add(stored.instance_id)
            upsert_instance(con, stored)
            n_added += 1

    print(
        f"  Z_{ell}xZ_{m}: {n_raw} raw → {n_added} unique k≥2 "
        f"(skipped {n_k_zero} k=0, {n_raw - n_added - n_k_zero} dedup-or-collide)"
    )
    return n_added


def main() -> None:
    t0 = time.time()
    print(f"sample_neighborhoods → {DB_PATH}")
    total = 0
    # Multi-prime mixed-rank G_odd (round-1 blind spot). Use Z_*×Z_3 / Z_*×Z_5
    # orientations to match bb_90's published `(ell, m) = (15, 3)` so the
    # bb_90 seed polynomials apply directly.
    total += _sample_group(15, 3, _bb90_perturbations, "bb_neigh_z15z3")
    total += _sample_group(21, 3, _bb90_perturbations, "bb_neigh_z21z3")
    total += _sample_group(15, 5, _bb90_perturbations, "bb_neigh_z15z5")
    # Gross-scale.
    total += _sample_group(12, 6, _gross_perturbations, "bb_neigh_gross")
    total += _sample_group(12, 12, _bb288_perturbations, "bb_neigh_bb288")
    dt = time.time() - t0
    print(f"done: {total} new canonical instances in {dt:.1f}s")


if __name__ == "__main__":
    main()

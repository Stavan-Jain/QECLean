"""A18 — sampled canonical enumeration for groups too large to exhaust.

For each requested group Z_ell x Z_m, draw uniform random weight-3
(A, B) support pairs, keep those with k >= --k-min, canonicalize the
keepers with the same `canonical_bits` machinery `bb-lab enumerate`
uses, and upsert them into the corpus DuckDB with code_id prefix
`bb_samp_` (so sampled — non-exhaustive — provenance stays visible
next to the exhaustive `bb_enum_` rows).

Sampling is orbit-size-biased (larger orbits are hit more often),
which for breadth purposes is indistinguishable from uniform: almost
all orbits under Aut(G) x translation x swap have full size.

Usage:
  uv run python a18_sample_enum.py --db data/bb_instances.duckdb \
      --group 7,8,1500 --group 6,10,1500 [--seed 20260707]
"""

from __future__ import annotations

import argparse
import time

import numpy as np

from bb_lab.automorphism import automorphisms
from bb_lab.canonical import CanonicalPair, build_perm_table, canonical_bits, _bits_to_support
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.group import ZmZn
from bb_lab.linalg import rank_f2
from bb_lab.poly import Poly
from bb_lab.store import StoredInstance, canonical_hash, connect, upsert_instance


def sample_group(
    con,
    ell: int,
    m: int,
    target: int,
    *,
    k_min: int,
    seed: int,
    time_cap: float,
) -> tuple[int, int]:
    """Sample canonical BB instances on Z_ell x Z_m until `target` new
    rows are inserted, the time cap expires, or the try budget runs out.
    Returns (inserted, tried)."""
    G = ZmZn(ell, m)
    N = G.cardinality
    label = G.label()

    t0 = time.time()
    auts = automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    print(
        f"  [{label}] |G|={N}, |Aut|={len(auts)}, |perms|={len(perms)} "
        f"(built in {time.time() - t0:.1f}s)",
        flush=True,
    )

    seen_ids: set[str] = {
        r[0]
        for r in con.execute(
            "SELECT instance_id FROM bb_instances WHERE group_struct = ?",
            [label],
        ).fetchall()
    }
    seen_pairs: set[tuple[int, int]] = set()

    rng = np.random.default_rng(seed + 1009 * ell + m)
    inserted = 0
    tried = 0
    k_rejects = 0
    max_tries = target * 400
    t_start = time.time()

    while inserted < target and tried < max_tries:
        if time.time() - t_start > time_cap:
            print(f"  [{label}] time cap {time_cap:.0f}s hit", flush=True)
            break
        tried += 1
        combo_A = np.sort(rng.choice(N, size=3, replace=False))
        combo_B = np.sort(rng.choice(N, size=3, replace=False))
        A_bits = int(sum(1 << int(i) for i in combo_A))
        B_bits = int(sum(1 << int(i) for i in combo_B))
        if (A_bits, B_bits) in seen_pairs:
            continue
        seen_pairs.add((A_bits, B_bits))

        A = Poly(support=frozenset(_bits_to_support(A_bits, G)), group=G)
        B = Poly(support=frozenset(_bits_to_support(B_bits, G)), group=G)
        checks = bb_check_matrices(A, B)
        params = code_params(checks)
        if params.k < k_min:
            k_rejects += 1
            continue

        can_A, can_B, orbit_size = canonical_bits(A_bits, B_bits, perms)
        A_supp = _bits_to_support(can_A, G)
        B_supp = _bits_to_support(can_B, G)
        A_str = Poly(support=frozenset(A_supp), group=G).canonical_string()
        B_str = Poly(support=frozenset(B_supp), group=G).canonical_string()
        iid = canonical_hash(label, A_str, B_str)
        if iid in seen_ids:
            continue
        seen_ids.add(iid)

        dim_ker_A = N - rank_f2(circulant(A))
        dim_ker_B = N - rank_f2(circulant(B))
        stored = StoredInstance(
            instance_id=iid,
            code_id=f"bb_samp_{label}_{iid[:8]}",
            group_struct=label,
            ell=ell,
            m=m,
            n=params.n,
            k=params.k,
            A_poly=A_str,
            B_poly=B_str,
            A_weight=3,
            B_weight=3,
            rank_HX=params.rank_HX,
            rank_HZ=params.rank_HZ,
            dim_ker_A=dim_ker_A,
            dim_ker_B=dim_ker_B,
            orbit_size=orbit_size,
        )
        upsert_instance(con, stored)
        inserted += 1
        if inserted % 250 == 0:
            dt = time.time() - t_start
            print(
                f"  [{label}] {inserted}/{target} kept, {tried} tried "
                f"(k<{k_min}: {k_rejects}), {dt:.0f}s",
                flush=True,
            )

    dt = time.time() - t_start
    print(
        f"  [{label}] DONE: {inserted} inserted, {tried} tried, "
        f"k-reject rate {k_rejects / max(tried, 1):.1%}, {dt:.0f}s",
        flush=True,
    )
    return inserted, tried


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", required=True)
    ap.add_argument(
        "--group",
        action="append",
        required=True,
        help="ell,m,target — repeatable",
    )
    ap.add_argument("--k-min", type=int, default=2)
    ap.add_argument("--seed", type=int, default=20260707)
    ap.add_argument("--time-cap", type=float, default=600.0, help="seconds per group")
    args = ap.parse_args()

    total = 0
    with connect(args.db) as con:
        for spec in args.group:
            ell, m, target = (int(x) for x in spec.split(","))
            ins, _ = sample_group(
                con, ell, m, target,
                k_min=args.k_min, seed=args.seed, time_cap=args.time_cap,
            )
            total += ins
    print(f"TOTAL inserted: {total}")


if __name__ == "__main__":
    main()

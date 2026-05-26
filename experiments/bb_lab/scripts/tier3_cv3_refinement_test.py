"""T3-A follow-up: test three candidate refinements against the
weight-4 violators of the C-v3 narrowed conjecture.

Refinements (per session discussion):

  R1 (odd-weight): add `weight(A), weight(B) both odd` to hypothesis.
      Equivalent to "A and B don't vanish on the trivial character"
      in F_2. Just an in/out-of-domain check.

  R2 (non-trivial min): same hypothesis, but RHS excludes the trivial
      orbit from min_O.

  R3 (mu_trivial = 0): equivalent to R1 in F_2 — listed for clarity.

For each in-scope (c ≥ 3) weight-4 pair on Z_6 × Z_6:
  - SAT-label to get d
  - record bound (= bb_radical_bound)
  - record R2 alternative bound
  - record violator status + refinement verdict

Parallelization: SAT solves run in a `multiprocessing.Pool` because
each call is independent and CPU-bound. Default 4 workers; tune with
--workers.

Run:
    uv run python scripts/tier3_cv3_refinement_test.py --limit 500 --workers 4
"""

from __future__ import annotations

import argparse
import math
import multiprocessing as mp
import time
from dataclasses import dataclass

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_depth,
)
from bb_lab.checks import bb_check_matrices
from bb_lab.enumerate_bb import enumerate_canonical_pairs
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    joint_support_subgroup_index,
    w_mu,
)
from bb_lab.sat_distance import x_distance


# ---------------------------------------------------------------------------
# Worker (must be picklable: top-level function, light state)
# ---------------------------------------------------------------------------


@dataclass
class WorkItem:
    idx: int
    ell: int
    m: int
    A_str: str
    B_str: str
    c: int
    n: int
    k: int
    bound: int
    max_d: int


@dataclass
class WorkResult:
    idx: int
    A_str: str
    B_str: str
    c: int
    n: int
    k: int
    bound: int
    d: int | None
    r2_bound: int
    wA: int
    wB: int
    elapsed: float


def _r2_bound(A: Poly, B: Poly, G: ZmZn) -> int:
    """R2: bb_radical_bound but min_O excludes the trivial orbit."""
    orbits = g_odd_frobenius_orbits(G)
    c = joint_support_subgroup_index(A, B, G)
    best = math.inf
    for orbit in orbits:
        rep = next(iter(orbit))
        if all(v == 0 for v in rep):
            continue
        if jacobson_radical_depth(A, orbit, G) == 0:
            continue
        if jacobson_radical_depth(B, orbit, G) == 0:
            continue
        wA = w_mu(A, orbit, 1, G)
        wB = w_mu(B, orbit, 1, G)
        if wA == float("inf") or wB == float("inf"):
            continue
        cand = min(wA, wB)
        if cand < best:
            best = cand
    if best == math.inf:
        return 0
    return math.ceil(best / max(c, 1))


def _worker(item: WorkItem) -> WorkResult:
    """Subprocess entry. Reconstructs the group + polys from strings."""
    G = ZmZn(item.ell, item.m)
    A = Poly.from_string(item.A_str, G)
    B = Poly.from_string(item.B_str, G)
    t0 = time.time()
    d: int | None
    try:
        res = x_distance(
            bb_check_matrices(A, B), weight_upper_bound=item.max_d
        )
        d = res.distance
    except Exception:
        d = None
    r2 = _r2_bound(A, B, G)
    return WorkResult(
        idx=item.idx,
        A_str=item.A_str,
        B_str=item.B_str,
        c=item.c,
        n=item.n,
        k=item.k,
        bound=item.bound,
        d=d,
        r2_bound=r2,
        wA=len(A.support),
        wB=len(B.support),
        elapsed=time.time() - t0,
    )


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ell", type=int, default=6)
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--weight", type=int, default=4)
    ap.add_argument("--limit", type=int, default=500)
    ap.add_argument("--max-d", type=int, default=10)
    ap.add_argument("--only-k-geq", type=int, default=2)
    ap.add_argument("--workers", type=int, default=4,
                    help="Parallel SAT workers (default 4)")
    args = ap.parse_args()

    G = ZmZn(args.ell, args.m)
    print(f"G = Z_{args.ell} × Z_{args.m}, weight={args.weight}, "
          f"limit={args.limit}, workers={args.workers}")

    # Stage 1: enumerate in-scope items (cheap; sequential).
    print("Enumerating in-scope instances …")
    t0 = time.time()
    enumerator = enumerate_canonical_pairs(
        G, weight=args.weight,
        only_k_geq=args.only_k_geq if args.only_k_geq > 0 else None,
    )
    items: list[WorkItem] = []
    for inst in enumerator:
        A = Poly(group=G, support=inst.canonical.A_support)
        B = Poly(group=G, support=inst.canonical.B_support)
        c = joint_support_subgroup_index(A, B, G)
        if c < 3:
            continue
        bound = bb_radical_bound(A, B, G)
        items.append(WorkItem(
            idx=len(items), ell=args.ell, m=args.m,
            A_str=A.canonical_string(),
            B_str=B.canonical_string(),
            c=c, n=inst.n, k=inst.k,
            bound=bound, max_d=args.max_d,
        ))
        if len(items) >= args.limit:
            break
    print(f"  {len(items)} in-scope, enum {time.time()-t0:.1f}s")

    # Stage 2: parallel SAT + R2 bound.
    print(f"\nSAT-labeling + R2 in parallel ({args.workers} workers) …")
    results: list[WorkResult] = []
    t0 = time.time()
    if args.workers <= 1:
        for it in items:
            results.append(_worker(it))
    else:
        with mp.Pool(processes=args.workers) as pool:
            for i, r in enumerate(pool.imap_unordered(_worker, items, chunksize=4)):
                results.append(r)
                if (i + 1) % 50 == 0:
                    print(f"  {i+1}/{len(items)} ({time.time()-t0:.1f}s)")
    results.sort(key=lambda r: r.idx)
    print(f"  done, {time.time()-t0:.1f}s")

    # Stage 3: analyze.
    violators = [r for r in results if r.d is not None and r.bound > r.d]
    tight = [r for r in results if r.d is not None and r.bound == r.d]
    loose = [r for r in results if r.d is not None and 0 < r.bound < r.d]
    errors = [r for r in results if r.d is None]

    print(
        f"\nTotals: {len(results)} tested, "
        f"{len(violators)} violations, "
        f"{len(tight)} tight, {len(loose)} loose, "
        f"{len(errors)} errors"
    )

    if not violators:
        print("No violators in this batch — nothing to refine against.")
        return

    print("\n### Per-violator refinement analysis ###")
    print(
        f"{'A':<32} {'B':<32} {'wA':>3} {'wB':>3} "
        f"{'bound':>5} {'d':>3} {'R1':>5} {'R2':>5}"
    )
    r1_excludes = r1_includes = 0
    r2_saves = r2_still_violates = r2_vacuous = 0
    for v in violators:
        odd_A = v.wA % 2 == 1
        odd_B = v.wB % 2 == 1
        r1_in = odd_A and odd_B
        if r1_in:
            r1_includes += 1
            r1_str = "in"
        else:
            r1_excludes += 1
            r1_str = "out"
        if v.r2_bound == 0:
            r2_vacuous += 1
            r2_str = "vac"
        elif v.r2_bound <= v.d:
            r2_saves += 1
            r2_str = str(v.r2_bound)
        else:
            r2_still_violates += 1
            r2_str = f"!{v.r2_bound}"
        print(
            f"{v.A_str:<32} {v.B_str:<32} {v.wA:>3} {v.wB:>3} "
            f"{v.bound:>5} {v.d:>3} {r1_str:>5} {r2_str:>5}"
        )

    print("\n### Summary ###")
    print(f"  violators in batch: {len(violators)}")
    print(f"\n  R1 (odd-weight hypothesis):")
    print(f"    excluded → no longer a counterexample: {r1_excludes}")
    print(f"    still in domain → unresolved:          {r1_includes}")
    print(f"\n  R2 (exclude trivial orbit from min):")
    print(f"    R2 bound ≤ d (refinement saves):       {r2_saves}")
    print(f"    R2 bound > d (still violates):         {r2_still_violates}")
    print(f"    R2 bound = 0 (claim vacuous):          {r2_vacuous}")


if __name__ == "__main__":
    main()

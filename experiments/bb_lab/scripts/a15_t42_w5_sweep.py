#!/usr/bin/env python3
"""A15 track T4.2 — the w = 5 sweep (falsify-first gate for the d > 12 lane).

Question (A15 plan §T4.2): on floor-bearing frames with |G| >= 41 (the
D1∧D2 counting bound 2·2·C(5,2) = 40 <= |G|−1), do the class hypotheses

    W5 (|A| = |B| = 5, odd => PAR)
    D1 (both Sidon), D2 (dA ∩ dB = ∅)
    (iii) (A parity-mono in exactly x, B in exactly y)
    k > 0, Ann(A) ≠ 0 ≠ Ann(B)

come with d = 2w = 10?  Every structural hit is SAT-validated (exact
distance, cap 12) — the cover-cascade lesson.  Frobenius-square/quartic
relatedness and the A16 hypothesis flags are recorded as columns, NOT
gates: the falsify-first read is which flags explain any d < 10 rows.

Enumeration: per frame, translation-normalized (0 ∈ supp) mono-x Sidon
A-pool × mono-y Sidon B-pool, deduped to translation classes, then
FILTERED per side by the class gate Ann ≠ 0 (zero-divisorhood is
translation- and unit-invariant, and units dominate the pools — this
ordering is what makes |G| ≥ 54 tractable); zd-survivors are paired by
bitmask-disjoint difference sets, gated k > 0 (common annihilator,
k = 2·(|G| − rank[cA|cB]) by Frobenius duality), and only k-positive
pairs are deduped up to the code-equivalence maps that respect the
normalization (unit scalings x → x^u, y → y^v — includes global
negation — and independent retranslation of each side; + transpose-swap
on square frames).

Usage (from experiments/bb_lab):
    uv run python scripts/a15_t42_w5_sweep.py --selftest
    uv run python scripts/a15_t42_w5_sweep.py [--gmax 60] [--sat-cap 150]
Output: data/a15/t42_w5_sweep.jsonl + per-frame summary lines.
"""

from __future__ import annotations

import argparse
import itertools
import json
import multiprocessing as mp
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.diffset_predicates import frobenius_square, is_translate
from bb_lab.group import AbelianGroup
from bb_lab.linalg import rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance

# ---------------------------------------------------------------- frames

def floor_bearing_frames(gmin: int, gmax: int) -> list[tuple[int, int]]:
    """Unordered rank-2 frames (l <= m), 4∤l, 4∤m, gmin <= l*m <= gmax.

    One orientation suffices: on a fixed frame the opposite mono-
    assignment is the (A,B)-swap of the transposed frame, and both are
    code-equivalent (d_X = d_Z for BB).
    """
    out = []
    for ell in range(2, gmax + 1):
        if ell % 4 == 0:
            continue
        for m in range(ell, gmax + 1):
            if m % 4 == 0 or not (gmin <= ell * m <= gmax):
                continue
            out.append((ell, m))
    return sorted(out, key=lambda t: (t[0] * t[1], t))


# ------------------------------------------------------------ gate stack

def parity_projections(supp, rank: int) -> tuple[frozenset, ...]:
    """Per-axis parity-collapsed projections (the (iii) projections)."""
    out = []
    for ax in range(rank):
        c: Counter = Counter(g[ax] for g in supp)
        out.append(frozenset(x for x, n in c.items() if n % 2))
    return tuple(out)


def mono_axes(supp, rank: int) -> list[int]:
    return [i for i, s in enumerate(parity_projections(supp, rank)) if len(s) == 1]


def diff_multiset_free(G, supp) -> tuple[bool, frozenset]:
    """(is Sidon, difference set)."""
    lst = [G.sub(a, b) for a in supp for b in supp if a != b]
    return len(lst) == len(set(lst)), frozenset(lst)


def enumerate_pool(G, w: int, axis: int, idx: dict) -> list[tuple[tuple, int]]:
    """Translation-normalized (0 ∈ supp) w-supports, parity-mono in
    exactly `axis`, Sidon.  Returns (support, diffset-bitmask) pairs."""
    zero = (0,) * G.rank
    others = [g for g in G if g != zero]
    pool = []
    for rest in itertools.combinations(others, w - 1):
        supp = (zero, *rest)
        if mono_axes(supp, G.rank) != [axis]:
            continue
        ok, ds = diff_multiset_free(G, supp)
        if not ok:
            continue
        mask = 0
        for d in ds:
            mask |= 1 << idx[d]
        pool.append((supp, mask))
    return pool


def translation_classes(G, pool):
    """Dedupe zero-normalized supports up to translation.  A Sidon
    support has trivial translation stabilizer (a nontrivial stabilizer
    ⟨t⟩ forces supp to be a coset of an order-5 subgroup, whose internal
    differences repeat), so each class appears exactly w times in the
    zero-normalized pool; diffset masks are translation-invariant."""
    seen: dict[tuple, tuple] = {}
    for supp, mask in pool:
        key = min(
            tuple(sorted(G.sub(g, t) for g in supp)) for t in supp)
        if key not in seen:
            seen[key] = (supp, mask)
    return list(seen.values())


# ------------------------------------------------------- canonical dedupe

def _unit_maps(G) -> list[tuple[int, int]]:
    ell, m = G.orders
    us = [u for u in range(1, ell) if _gcd(u, ell) == 1]
    vs = [v for v in range(1, m) if _gcd(v, m) == 1]
    return [(u, v) for u in us for v in vs]


def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


def canon_key(G, sa, sb) -> tuple:
    """Min serialized form over unit scalings × per-side retranslation
    (+ transpose-swap on square frames)."""
    ell, m = G.orders
    variants = [(sa, sb)]
    if ell == m:
        tr = lambda s: tuple((g[1], g[0]) for g in s)
        variants.append((tr(sb), tr(sa)))  # swap A<->B + transpose axes
    best = None
    for va, vb in variants:
        for u, v in _unit_maps(G):
            ma = [((u * g[0]) % ell, (v * g[1]) % m) for g in va]
            mb = [((u * g[0]) % ell, (v * g[1]) % m) for g in vb]
            ka = min(
                tuple(sorted(((x - t0) % ell, (y - t1) % m) for x, y in ma))
                for t0, t1 in ma)
            kb = min(
                tuple(sorted(((x - t0) % ell, (y - t1) % m) for x, y in mb))
                for t0, t1 in mb)
            key = (ka, kb)
            if best is None or key < best:
                best = key
    return best


# ---------------------------------------------------- member validation

def validate_member(args: tuple) -> dict:
    """SAT-validate one canonical member (top-level for multiprocessing).

    `args = (sa, sb, ell, m, sat_ub)`; returns the jsonl row dict."""
    sa, sb, ell, m, sat_ub, do_sat = args
    G = AbelianGroup((ell, m))
    A = Poly.from_support(sa, G)
    B = Poly.from_support(sb, G)
    checks = bb_check_matrices(A, B)
    k = code_params(checks).k
    A2, B2 = frobenius_square(A), frobenius_square(B)
    flags = {
        "frob2": is_translate(A, B2) or is_translate(B, A2),
        "frob4": is_translate(A, frobenius_square(B2))
                 or is_translate(B, frobenius_square(A2)),
    }
    row = {
        "frame": [ell, m], "n": 2 * ell * m, "k": k,
        "A": A.canonical_string(), "B": B.canonical_string(),
        "flags": flags,
    }
    if not do_sat:
        row["d"] = None  # over SAT budget — reported, not silently dropped
        return row
    try:
        res = x_distance(checks, weight_lower_bound=2,
                         weight_upper_bound=sat_ub)
        row["d"] = res.distance
    except RuntimeError:
        row["d"] = f">{sat_ub}"  # all weights <= cap UNSAT
    return row


# ------------------------------------------------------------- per frame

def diff_index_table(G, elems, idx) -> np.ndarray:
    """dt[r, c] = idx[elems[r] − elems[c]], built once per frame; the
    circulant of any support is then the O(n²) numpy gather
    vec[dt] (circulant() itself is a Python double loop — too slow to
    call once per pool class)."""
    n = len(elems)
    dt = np.empty((n, n), dtype=np.int32)
    for r, g in enumerate(elems):
        for c, h in enumerate(elems):
            dt[r, c] = idx[G.sub(g, h)]
    return dt


def sweep_frame(ell: int, m: int, w: int, sat_cap: int, out,
                sat_ub: int = 12, sat_jobs: int = 1) -> dict:
    t0 = time.time()
    G = AbelianGroup((ell, m))
    n = ell * m
    elems = list(G)
    idx = {g: i for i, g in enumerate(elems)}

    poolA = translation_classes(G, enumerate_pool(G, w, 0, idx))  # A mono-x
    poolB = translation_classes(G, enumerate_pool(G, w, 1, idx))  # B mono-y

    # Per-side class gate Ann ≠ 0 BEFORE the quadratic pairing (units
    # dominate the pools; zero-divisorhood is translation-invariant so
    # filtering classes is sound).  Cached circulants feed the k-test.
    have_both = bool(poolA) and bool(poolB)
    dt = diff_index_table(G, elems, idx) if have_both else None

    def zd_filter(pool):
        keep = []
        vec = np.zeros(n, dtype=np.uint8)
        for supp, mask in pool:
            vec[:] = 0
            vec[[idx[s] for s in supp]] = 1
            circ = vec[dt]
            if rank_f2(circ) < n:
                keep.append((supp, mask, circ))
        return keep

    zdA = zd_filter(poolA) if have_both else []
    zdB = zd_filter(poolB) if have_both and zdA else []

    # D2 pairing (bitmask disjoint) + k > 0 (common annihilator), then
    # canonical dedupe of the k-positive survivors only.
    n_pairs = 0
    n_kpos = 0
    reps: dict[tuple, tuple] = {}
    for sa, ma, ca in zdA:
        for sb, mb, cb in zdB:
            if ma & mb:
                continue
            n_pairs += 1
            k = 2 * (n - rank_f2(np.hstack([ca, cb])))
            if k == 0:
                continue
            n_kpos += 1
            key = canon_key(G, sa, sb)
            if key not in reps:
                reps[key] = (sa, sb)

    if reps:  # surface structural hits before the (slow) SAT stage
        print(json.dumps({"frame": f"Z{ell}xZ{m}", "stage": "structural",
                          "members": len(reps)}), flush=True)

    # members: flags + SAT (k recomputed of-record via code_params).
    # SAT budget = the first sat_cap members; --sat-jobs N validates
    # members in parallel worker processes (rows stream as they finish).
    member_args = [
        (sa, sb, ell, m, sat_ub, i < sat_cap)
        for i, (sa, sb) in enumerate(reps.values())
    ]
    rows = []

    def emit(row: dict) -> None:
        rows.append(row)
        out.write(json.dumps(row) + "\n")
        out.flush()

    if sat_jobs > 1 and len(member_args) > 1:
        ctx = mp.get_context("spawn")
        with ctx.Pool(min(sat_jobs, len(member_args))) as pool:
            for row in pool.imap_unordered(validate_member, member_args):
                emit(row)
    else:
        for a in member_args:
            emit(validate_member(a))
    sat_done = sum(1 for r in rows if r["d"] is not None)

    ds = Counter(str(r["d"]) for r in rows if r["d"] is not None)
    summary = {
        "frame": f"Z{ell}xZ{m}", "G": n,
        "poolA": len(poolA), "poolB": len(poolB),
        "zdA": len(zdA), "zdB": len(zdB),
        "d2_pairs": n_pairs, "kpos_pairs": n_kpos,
        "members": len(reps),
        "d_hist": dict(sorted(ds.items())),
        "sat_done": sat_done,
        "secs": round(time.time() - t0, 1),
    }
    print(json.dumps(summary), flush=True)
    return summary


# -------------------------------------------------------------- selftest

def selftest() -> None:
    """Pipeline sanity at w = 3 on Z6xZ6: the gross base must survive
    every gate and SAT to d = 6 = 2w."""
    G = AbelianGroup((6, 6))
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    assert mono_axes(A.support, 2) == [0], "gross A not mono-x?!"
    assert mono_axes(B.support, 2) == [1], "gross B not mono-y?!"
    okA, dA = diff_multiset_free(G, A.support)
    okB, dB = diff_multiset_free(G, B.support)
    assert okA and okB and not (dA & dB), "gross D1/D2 fail?!"
    checks = bb_check_matrices(A, B)
    assert code_params(checks).k == 12
    n = 36
    assert rank_f2(circulant(A)) < n and rank_f2(circulant(B)) < n
    # fast paths vs reference: gather-circulant and the direct k formula
    elems = list(G)
    idx = {g: i for i, g in enumerate(elems)}
    dt = diff_index_table(G, elems, idx)
    for P in (A, B):
        vec = np.zeros(n, dtype=np.uint8)
        vec[[idx[s] for s in P.support]] = 1
        assert np.array_equal(vec[dt], circulant(P)), "gather-circulant mismatch"
    k_direct = 2 * (n - rank_f2(np.hstack([circulant(A), circulant(B)])))
    assert k_direct == 12, f"direct k formula gives {k_direct} != 12"
    res = x_distance(checks, weight_lower_bound=2, weight_upper_bound=8)
    assert res.distance == 6, f"gross base d = {res.distance} != 6?!"
    # canonical dedupe sanity: unit map (5,5) = negation gives same key
    neg = lambda s: tuple(G.neg(g) for g in s)
    assert canon_key(G, tuple(A.support), tuple(B.support)) == \
        canon_key(G, neg(tuple(A.support)), neg(tuple(B.support)))
    print("SELFTEST PASS (w=3 pipeline: gross base gates + d=6 + canon)")


# ------------------------------------------------------------------ main

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--gmin", type=int, default=41)
    ap.add_argument("--gmax", type=int, default=60)
    ap.add_argument("--w", type=int, default=5)
    ap.add_argument("--sat-cap", type=int, default=150,
                    help="max SAT calls per frame")
    ap.add_argument("--sat-ub", type=int, default=12,
                    help="distance search cap (records '>ub' beyond)")
    ap.add_argument("--sat-jobs", type=int, default=1,
                    help="parallel worker processes for member SAT calls")
    ap.add_argument("--frames", type=str, default=None,
                    help="comma list like 6x7,3x14 to override the scan")
    ap.add_argument("--out", type=str,
                    default="data/a15/t42_w5_sweep.jsonl")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    if args.frames:
        frames = []
        for tok in args.frames.split(","):
            a, b = tok.lower().split("x")
            frames.append((int(a), int(b)))
    else:
        frames = floor_bearing_frames(args.gmin, args.gmax)

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    print(f"frames: {[f'{a}x{b}' for a, b in frames]}", flush=True)
    summaries = []
    with outp.open("a") as out:
        for ell, m in frames:
            summaries.append(
                sweep_frame(ell, m, args.w, args.sat_cap, out,
                            sat_ub=args.sat_ub, sat_jobs=args.sat_jobs))

    total = sum(s["members"] for s in summaries)
    print(f"\nTOTAL members: {total} across {len(frames)} frames; "
          f"rows appended to {outp}")


if __name__ == "__main__":
    main()

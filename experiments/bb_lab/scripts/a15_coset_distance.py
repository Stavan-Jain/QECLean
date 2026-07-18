#!/usr/bin/env python3
"""Exact BB code distance via per-coset SAT + translation-orbit transport
(the A14 S4 coset-query idea ported from covers to plain distance).

Why: the full-space distance instance ("some nontrivial logical of
weight <= w") scales ~7x per weight increment (Entry 15 calibration) —
UNSAT at w = 13 is unreachable.  Fixing the LOGICAL CLASS turns the OR
over 2^k − 1 classes into k pinned XOR constraints, and each coset
instance is dramatically easier.  The translation group G acts on the
class group ker(H_Z)/rowspan(H_X) ≅ F₂^k preserving coset min-weight,
so only one query per G-orbit is needed (k = 12, |G| = 63: 4095 → ~65
reps).

Protocol (exact d, descending):
  phase A: query orbit reps at w = ub until one SATs — establishes a
           self-found witness (do not trust external upper bounds);
  phase B: query every unresolved rep at w = best − 1; SAT → better
           witness, descend; UNSAT → rep resolved for all lower rounds
           (no vector ≤ w in a coset ⟹ none ≤ w' < w).
  Terminates when all reps are resolved at best − 1 ⟹ d = best exactly.

Usage (from experiments/bb_lab):
    uv run python scripts/a15_coset_distance.py --selftest
    uv run python scripts/a15_coset_distance.py \
        '{"frame": [7, 9], "A": "...", "B": "..."}' --start-ub 14
"""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

import pycryptosat
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

from bb_lab.checks import CheckMatrices, bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, quotient_complement_basis, rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import find_logical_z

from a15_t42_mc_falsifier import mc_min_logical  # phase-A witness seed


# ----------------------------------------------------- class structure

def x_class_reps(checks: CheckMatrices) -> np.ndarray:
    """Rows: k vectors in ker(H_Z) spanning ker(H_Z)/rowspan(H_X)
    (X-logical class representatives) — the mirror of find_logical_z."""
    return quotient_complement_basis(checks.H_X, nullspace_f2(checks.H_Z))


def translation_perm(G: AbelianGroup, t: tuple, n: int) -> np.ndarray:
    """Index permutation of the 2n qubits for e ↦ x^t · e (both blocks
    shift by t; circulant checks are translation-covariant, so this
    preserves ker(H_Z), rowspan(H_X), and weight)."""
    elems = list(G)
    idx = {g: i for i, g in enumerate(elems)}
    p = np.empty(2 * n, dtype=np.int64)
    for i, g in enumerate(elems):
        j = idx[G.add(g, t)]
        p[j] = i          # (t·e)[j] = e[i] with j = idx(g + t)
        p[n + j] = n + i
    return p


def signature_action(G: AbelianGroup, checks: CheckMatrices,
                     L_Z: np.ndarray, S: np.ndarray
                     ) -> tuple[list[np.ndarray], np.ndarray]:
    """Matrices of the two generator translations acting on class
    signatures σ(e) = L_Z·e ∈ F₂^k, plus the change-of-basis P = L_Z Sᵀ.

    σ(t·s_j) = column j of Q_t; classes transform σ ↦ Q_t P⁻¹ σ (P maps
    quotient coordinates to signatures; pairing with rowspan(H_Z) — and
    hence with Z-stabilizers — vanishes on ker(H_Z), so signatures are
    class functions)."""
    n = checks.group.cardinality
    k = S.shape[0]
    P = (L_Z @ S.T) % 2
    assert rank_f2(P) == k, "logical pairing degenerate?!"
    mats = []
    gens = []
    rank = G.rank
    for ax in range(rank):
        t = tuple(1 if i == ax else 0 for i in range(rank))
        gens.append(t)
        perm = translation_perm(G, t, n)
        Q = (L_Z @ S[:, perm].T) % 2  # transported reps' signatures
        mats.append((Q @ inv_f2(P)) % 2)
    return mats, np.array(gens)


def inv_f2(M: np.ndarray) -> np.ndarray:
    """Inverse of a square F₂ matrix via Gauss-Jordan."""
    k = M.shape[0]
    A = np.concatenate([(M & 1).astype(np.uint8), np.eye(k, dtype=np.uint8)],
                       axis=1)
    row = 0
    for col in range(k):
        piv = row + int(np.flatnonzero(A[row:, col])[0])
        A[[row, piv]] = A[[piv, row]]
        mask = A[:, col] == 1
        mask[row] = False
        A[mask] ^= A[row]
        row += 1
    return A[:, k:]


def orbit_reps(mats: list[np.ndarray], orders: list[int], k: int
               ) -> list[tuple[int, int]]:
    """(rep, orbit_size) per orbit of the abelian translation action on
    F₂^k \\ {0}. Signatures encoded as ints (bit i = coordinate i)."""
    def apply(M: np.ndarray, sig: int) -> int:
        v = np.fromiter(((sig >> i) & 1 for i in range(k)),
                        dtype=np.uint8, count=k)
        w = (M @ v) % 2
        out = 0
        for i in range(k):
            if w[i]:
                out |= 1 << i
        return out

    seen: set[int] = set()
    reps: list[tuple[int, int]] = []
    for sig in range(1, 1 << k):
        if sig in seen:
            continue
        orbit = {sig}
        frontier = [sig]
        while frontier:
            s = frontier.pop()
            for M in mats:
                s2 = apply(M, s)
                if s2 not in orbit:
                    orbit.add(s2)
                    frontier.append(s2)
        seen |= orbit
        reps.append((sig, len(orbit)))
    assert sum(sz for _, sz in reps) == (1 << k) - 1
    return reps


# ------------------------------------------------------- coset queries

def coset_query(checks: CheckMatrices, L_Z: np.ndarray, sig: int,
                weight: int) -> np.ndarray | None:
    """Witness of weight ≤ `weight` in the logical class with signature
    `sig` (bits over L_Z rows), or None (UNSAT — none exists).

    Same instance as sat_distance's, with the k-way OR replaced by k
    pinned XORs: ⟨L_i, e⟩ = sig_i."""
    n2 = checks.num_qubits
    pool = IDPool()
    qubit_vars = [pool.id() for _ in range(n2)]
    solver = pycryptosat.Solver()

    for row in checks.H_Z:
        idx = np.flatnonzero(row)
        if idx.size:
            solver.add_xor_clause([qubit_vars[i] for i in idx], False)

    for i, L in enumerate(L_Z):
        idx = np.flatnonzero(L)
        want = bool((sig >> i) & 1)
        if idx.size == 0:
            if want:
                return None  # unsatisfiable pin on an empty row
            continue
        solver.add_xor_clause([qubit_vars[j] for j in idx], want)

    if weight < n2:
        card = CardEnc.atmost(lits=qubit_vars, bound=weight,
                              vpool=pool, encoding=EncType.seqcounter)
        for cl in card.clauses:
            solver.add_clause(cl)

    sat, model = solver.solve()
    if not sat:
        return None
    v = np.array([1 if model[qv] else 0 for qv in qubit_vars],
                 dtype=np.uint8)
    # self-certify before returning
    assert not (checks.H_Z @ v % 2).any()
    assert int(v.sum()) <= weight
    got = 0
    for i, L in enumerate(L_Z):
        if (L @ v) % 2:
            got |= 1 << i
    assert got == sig, "witness landed in the wrong class?!"
    return v


# ------------------------------------------------------------ protocol

def _query_worker(args: tuple) -> tuple[int, np.ndarray | None, float]:
    """(sig, witness-or-None, secs) — top-level for multiprocessing."""
    checks, L_Z, sig, weight = args
    t0 = time.time()
    v = coset_query(checks, L_Z, sig, weight)
    return sig, v, time.time() - t0


def exact_distance(G: AbelianGroup, checks: CheckMatrices,
                   start_ub: int, jobs: int = 1,
                   verbose: bool = True) -> tuple[int, np.ndarray]:
    """(exact d, minimum-weight witness) by descending coset rounds."""
    L_Z = find_logical_z(checks)
    S = x_class_reps(checks)
    k = S.shape[0]
    mats, gens = signature_action(G, checks, L_Z, S)
    for M, order in zip(mats, G.orders):
        acc = np.eye(k, dtype=np.uint8)
        for _ in range(order):
            acc = (M @ acc) % 2
        assert np.array_equal(acc % 2, np.eye(k, dtype=np.uint8)), \
            "translation action order mismatch"
    reps = orbit_reps(mats, list(G.orders), k)
    if verbose:
        print(f"k = {k}: {(1 << k) - 1} classes → {len(reps)} orbit reps "
              f"(sizes {sorted(set(sz for _, sz in reps))})", flush=True)

    # phase A: MC-seeded witness (self-certified inside mc_min_logical's
    # caller contract: re-checked here) — avoids burning w = start_ub
    # UNSAT queries on classes ordered before the witness's class.
    unresolved = [sig for sig, _ in reps]
    t0 = time.time()
    best_w, best_v = mc_min_logical(checks.H_Z, L_Z, wmax=start_ub,
                                    iters=20000, seed=42)
    assert best_v is not None and best_w <= start_ub, (
        f"MC found nothing <= {start_ub} (best {best_w}) — raise "
        f"--start-ub or check the member")
    assert not (checks.H_Z @ best_v % 2).any()
    assert (L_Z @ best_v % 2).any()
    if verbose:
        print(f"  [A] MC witness weight {best_w} "
              f"({time.time()-t0:.1f}s)", flush=True)

    # phase B: descending rounds. A rep UNSAT at target is resolved for
    # every lower target too; any SAT strictly lowers best_w, so each
    # round descends until every rep is resolved at best_w − 1.
    while True:
        target = best_w - 1
        work = [(checks, L_Z, sig, target) for sig in unresolved]
        nxt = []
        done = 0

        def handle(res: tuple) -> None:
            nonlocal best_w, best_v, done
            sig, v, secs = res
            done += 1
            if v is None:
                if verbose:
                    print(f"  [B w<={target}] {done}/{len(work)} "
                          f"class {sig:#x}: UNSAT ({secs:.1f}s)", flush=True)
                return
            w = int(v.sum())
            if verbose:
                print(f"  [B w<={target}] {done}/{len(work)} "
                      f"class {sig:#x}: SAT wt {w} ({secs:.1f}s)", flush=True)
            nxt.append(sig)
            if w < best_w:
                best_w, best_v = w, v

        if jobs > 1 and len(work) > 1:
            ctx = mp.get_context("spawn")
            with ctx.Pool(min(jobs, len(work))) as pool:
                for res in pool.imap_unordered(_query_worker, work):
                    handle(res)
        else:
            for a in work:
                handle(_query_worker(a))
        unresolved = nxt
        if not unresolved:
            return best_w, best_v


# ------------------------------------------------------------ selftest

def selftest() -> None:
    """Gross BASE [[72,12,6]] (Z₆×Z₆) — d = 6 is kernel-certified in
    the repo; the coset method must reproduce it exactly."""
    G = AbelianGroup((6, 6))
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    checks = bb_check_matrices(A, B)
    assert code_params(checks).k == 12
    t0 = time.time()
    d, v = exact_distance(G, checks, start_ub=6)
    assert d == 6, f"coset method got d = {d} != 6 on the gross base?!"
    print(f"SELFTEST PASS (gross base exact d = 6 via coset+orbit, "
          f"{time.time()-t0:.1f}s)")


# ---------------------------------------------------------------- main

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("row", nargs="?", help="member row JSON with frame/A/B")
    ap.add_argument("--start-ub", type=int, default=14,
                    help="phase-A witness search weight (from MC mc_min)")
    ap.add_argument("--jobs", type=int, default=1,
                    help="parallel workers for the per-round coset queries")
    ap.add_argument("--floor-check", type=int, default=None, metavar="W",
                    help="single round at weight W over all orbit reps; "
                         "all-UNSAT proves d >= W+1 (no descent)")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    row = json.loads(args.row)
    ell, m = row["frame"]
    G = AbelianGroup((ell, m))
    A = Poly.from_string(row["A"], G)
    B = Poly.from_string(row["B"], G)
    checks = bb_check_matrices(A, B)
    k = code_params(checks).k
    print(f"Z{ell}xZ{m}: n = {2*ell*m}, k = {k}; A = {row['A']}; "
          f"B = {row['B']}", flush=True)
    if args.floor_check is not None:
        W = args.floor_check
        L_Z = find_logical_z(checks)
        S = x_class_reps(checks)
        kk = S.shape[0]
        mats, _ = signature_action(G, checks, L_Z, S)
        reps = orbit_reps(mats, list(G.orders), kk)
        print(f"floor check at w <= {W}: {len(reps)} orbit reps",
              flush=True)
        work = [(checks, L_Z, sig, W) for sig, _ in reps]
        hits = []
        t0 = time.time()
        ctx = mp.get_context("spawn")
        with ctx.Pool(min(args.jobs, len(work))) as pool:
            for sig, v, secs in pool.imap_unordered(_query_worker, work):
                tag = "UNSAT" if v is None else f"SAT wt {int(v.sum())}"
                print(f"  [F w<={W}] class {sig:#x}: {tag} ({secs:.1f}s)",
                      flush=True)
                if v is not None:
                    hits.append((sig, int(v.sum())))
        verdict = (f"d >= {W+1} PROVEN (all {len(reps)} orbit reps UNSAT)"
                   if not hits else f"REFUTED: witnesses {hits}")
        print(json.dumps({
            "frame": [ell, m], "k": k, "floor_check_w": W,
            "orbit_reps": len(reps), "sat_hits": hits,
            "verdict": verdict, "secs": round(time.time() - t0, 1),
        }), flush=True)
        return

    t0 = time.time()
    d, v = exact_distance(G, checks, start_ub=args.start_ub,
                          jobs=args.jobs)
    print(json.dumps({
        "frame": [ell, m], "n": 2 * ell * m, "k": k,
        "A": row["A"], "B": row["B"],
        "d_exact": d, "witness": np.flatnonzero(v).tolist(),
        "secs": round(time.time() - t0, 1),
    }), flush=True)


if __name__ == "__main__":
    main()

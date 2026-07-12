#!/usr/bin/env python3
"""A15 T4.2 — Monte-Carlo falsifier hunt over w = 5 class members.

QDistRnd-style random information-set search for low-weight X-logicals:
random column permutation → RREF of a ker(H_Z) basis → low-weight rows
that pair nontrivially with a logical-Z rep are WITNESSES (d_X ≤ wt).
A found witness is self-certifying (checked directly against H_Z and
L_Z before being written) — no SAT in the loop.  Not finding one makes
no claim; the capture probability of a fixed weight-w vector per
iteration is roughly dim·(1 − w/n)^dim-ish, so --iters 800 makes
missing a weight-≤9 falsifier unlikely (calibrate on the gross base:
its weight-6 logicals should surface within a few dozen iterations).

Usage (from experiments/bb_lab):
    uv run python scripts/a15_t42_mc_falsifier.py --selftest
    uv run python scripts/a15_t42_mc_falsifier.py \
        --in data/a15/t42_w5_census.jsonl --frames 5x15 \
        --wmax 9 --iters 800 --jobs 6 \
        --out data/a15/t42_w5_mc_5x15.jsonl
"""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rref_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import find_logical_z


def mc_min_logical(H_Z: np.ndarray, L_Z: np.ndarray, wmax: int,
                   iters: int, seed: int) -> tuple[int, np.ndarray | None]:
    """(best weight seen on any logical row, witness if ≤ wmax)."""
    rng = np.random.default_rng(seed)
    K = nullspace_f2(H_Z)  # rows span ker(H_Z) ⊇ logicals
    n = K.shape[1]
    best_w = n + 1
    best_v: np.ndarray | None = None
    for _ in range(iters):
        perm = rng.permutation(n)
        R, _ = rref_f2(K[:, perm])
        R = R[R.any(axis=1)]
        wts = R.sum(axis=1)
        for i in np.flatnonzero(wts < best_w):
            v = np.zeros(n, dtype=np.uint8)
            v[perm] = R[i]
            if (L_Z @ v % 2).any():  # nontrivial logical, not stabilizer
                best_w = int(wts[i])
                best_v = v
        if best_w <= wmax:
            break  # falsifier found — self-certifying, stop early
    return best_w, best_v


def hunt_member(args: tuple) -> dict:
    row_in, wmax, iters, seed = args
    ell, m = row_in["frame"]
    G = AbelianGroup((ell, m))
    A = Poly.from_string(row_in["A"], G)
    B = Poly.from_string(row_in["B"], G)
    checks = bb_check_matrices(A, B)
    L_Z = find_logical_z(checks)
    t0 = time.time()
    w, v = mc_min_logical(checks.H_Z, L_Z, wmax, iters, seed)
    row = {
        "frame": row_in["frame"], "A": row_in["A"], "B": row_in["B"],
        "k": row_in.get("k"), "flags": row_in.get("flags"),
        "mc_min": w, "falsifier": w <= wmax,
        "secs": round(time.time() - t0, 1),
    }
    if v is not None and w <= wmax:
        # self-certify before writing: in ker(H_Z), nontrivial, weight
        assert not (checks.H_Z @ v % 2).any(), "witness not in ker H_Z?!"
        assert (L_Z @ v % 2).any(), "witness is a stabilizer?!"
        assert int(v.sum()) == w
        row["witness"] = np.flatnonzero(v).tolist()
    return row


def selftest() -> None:
    """Gross base: MC must find weight-6 logicals quickly and nothing
    below 6 (its distance is 6, Lean-certified)."""
    G = AbelianGroup((6, 6))
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    checks = bb_check_matrices(A, B)
    L_Z = find_logical_z(checks)
    w, v = mc_min_logical(checks.H_Z, L_Z, wmax=6, iters=400, seed=7)
    assert w == 6, f"gross base MC min = {w} != 6 (d = 6 is certified)"
    assert v is not None and not (checks.H_Z @ v % 2).any()
    assert (L_Z @ v % 2).any()
    print("SELFTEST PASS (gross base: MC finds weight-6, nothing below)")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", type=str,
                    default="data/a15/t42_w5_census.jsonl")
    ap.add_argument("--frames", type=str, default=None,
                    help="comma list like 5x15 to restrict; default all")
    ap.add_argument("--wmax", type=int, default=9)
    ap.add_argument("--iters", type=int, default=800)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--seed", type=int, default=20260712)
    ap.add_argument("--out", type=str,
                    default="data/a15/t42_w5_mc.jsonl")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    want = None
    if args.frames:
        want = {tuple(int(t) for t in tok.lower().split("x"))
                for tok in args.frames.split(",")}
    members = []
    with open(args.inp) as f:
        for line in f:
            r = json.loads(line)
            if "A" not in r:
                continue
            if want is None or tuple(r["frame"]) in want:
                members.append(r)
    print(f"{len(members)} members from {args.inp}"
          f"{' (frames ' + args.frames + ')' if args.frames else ''}",
          flush=True)

    work = [(r, args.wmax, args.iters, args.seed + i)
            for i, r in enumerate(members)]
    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    hist: Counter = Counter()
    n_fals = 0
    t0 = time.time()
    with outp.open("a") as out:
        def emit(row: dict) -> None:
            nonlocal n_fals
            hist[row["mc_min"]] += 1
            n_fals += bool(row["falsifier"])
            out.write(json.dumps(row) + "\n")
            out.flush()
            if row["falsifier"]:
                print(json.dumps(row), flush=True)  # falsifiers to stdout

        if args.jobs > 1 and len(work) > 1:
            ctx = mp.get_context("spawn")
            with ctx.Pool(args.jobs) as pool:
                for i, row in enumerate(
                        pool.imap_unordered(hunt_member, work), 1):
                    emit(row)
                    if i % 100 == 0:
                        print(f"[{i}/{len(work)}] falsifiers so far: "
                              f"{n_fals}", flush=True)
        else:
            for a in work:
                emit(hunt_member(a))

    print(json.dumps({
        "members": len(work), "falsifiers": n_fals,
        "mc_min_hist": {str(k): hist[k] for k in sorted(hist)},
        "secs": round(time.time() - t0, 1),
    }), flush=True)


if __name__ == "__main__":
    main()

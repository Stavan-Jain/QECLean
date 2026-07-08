"""A11 CX — exhaustive light-b census + targeted neighborhood attack.

Closes the coverage gap in a11_cx_slice.py: its light-b census only took
boundaries of 1-/2-cell 2-chains, finding light stabilizers in 9/399 C-safe
cells.  Here b ranges over the ENTIRE Z-stabilizer space (column space of the
primal d2 = rowspace H_Z^base), enumerated by a chunked span sweep with
coefficient tracking (so a preimage y is free), feasible for base cells <= 24.
For every light b (0 < |b| < 2d, lightest --max-b kept): seam-minimal
preimage over the full ker d2 coset, then the exact relaxed slice minimum
    slice(b) = min over nontrivial base Z-logicals rho of |rho+h| + |rho+h'|
(SAT; relaxation of the tau-fiber pool => dips are necessary precursors of a
rung violation).  margin = slice(b) - 2d.

Subcommands:
    exhaust  --files ... [--max-b N] [--budget-sec S]     sweep C-safe cells
    cell     --frame Z3xZ7 --A .. --B .. --axis y [--d D] one-cell full probe
    neighbors --frame .. --A .. --B .. [--budget-sec S]
        single-monomial mutations of the pair, full C-safe + cover-ladder
        pipeline on each (jackpot check = d_cover directly), for attacking
        margin-0 cells.

Validation: reuses a11_cx_slice's selftested SAT encodings; census cross-
checked against the subset census (must be a superset) on the doc pair.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, quotient_complement_basis
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance

from a11_cx_slice import seam_split, slice_min, punctured_min
from a11_cx_hunt import eval_pair

CX_DIR = LAB_ROOT / "data" / "a11" / "cx"


def light_b_exhaustive(d2b: np.ndarray, two_d: int, max_b: int):
    """All light b in the column space of d2b, with one preimage y each.
    Returns list of (b, y0) sorted by |b|, capped at max_b lightest."""
    nq, nb = d2b.shape
    # independent columns (pivot columns) via incremental elimination
    piv: dict[int, tuple[np.ndarray, np.ndarray]] = {}   # leadidx -> (vec, y)
    basis: list[tuple[np.ndarray, np.ndarray]] = []      # (column, unit y)
    for j in range(nb):
        v = d2b[:, j].copy() % 2
        y = np.zeros(nb, dtype=np.uint8)
        y[j] = 1
        while True:
            nz = np.flatnonzero(v)
            if nz.size == 0:
                break
            p = int(nz[0])
            if p not in piv:
                piv[p] = (v, y)
                ej = np.zeros(nb, dtype=np.uint8)
                ej[j] = 1
                basis.append((d2b[:, j] % 2, ej))
                break
            pv, py = piv[p]
            v = v ^ pv
            y = y ^ py
    r = len(basis)
    Bmat = np.array([b for b, _ in basis], dtype=np.uint8)      # r x nq
    Ymat = np.array([y for _, y in basis], dtype=np.uint8)      # r x nb
    found: dict[bytes, tuple[int, np.ndarray, np.ndarray]] = {}
    total = 1 << r
    step = 1 << min(16, r)
    exps = np.arange(r, dtype=np.uint64)
    for start in range(0, total, step):
        idx = np.arange(start, min(start + step, total), dtype=np.uint64)
        coeff = ((idx[:, None] >> exps[None, :]) & 1).astype(np.uint8)
        blk = (coeff @ Bmat) % 2
        w = blk.sum(axis=1)
        sel = np.flatnonzero((w > 0) & (w < two_d))
        for i in sel:
            key = blk[i].tobytes()
            if key not in found:
                yv = (coeff[i] @ Ymat) % 2
                found[key] = (int(w[i]), blk[i].astype(np.uint8),
                              yv.astype(np.uint8))
    items = sorted(found.values(), key=lambda t: t[0])[:max_b]
    return [(b, y) for _, b, y in items], len(found), r


def probe_cell_exhaustive(frame: str, a_s: str, b_s: str, axis: str,
                          d: int, max_b: int = 120,
                          budget_sec: float = 300.0) -> dict:
    parts = frame.replace("Z", "").split("x")
    ell, m = int(parts[0]), int(parts[1])
    Gb0 = AbelianGroup((ell, m))
    A = Poly.from_string(a_s, Gb0)
    B = Poly.from_string(b_s, Gb0)
    Gb, chb, d2b, d2nc, d2cc = seam_split(ell, m, A, B, axis)
    nb = Gb.cardinality
    HXb = chb.H_X.astype(np.uint8)
    kerZb = nullspace_f2(chb.H_Z.astype(np.uint8))
    LXb = quotient_complement_basis(HXb, kerZb)
    twod = 2 * d
    ker2 = nullspace_f2(d2b) % 2
    dimk = ker2.shape[0]
    if dimk <= 14:
        idxs = np.arange(1 << dimk, dtype=np.uint64)
        coeff = ((idxs[:, None] >> np.arange(dimk, dtype=np.uint64)[None, :]) & 1
                 ).astype(np.uint8)
        ker_all = (coeff @ ker2) % 2 if dimk else np.zeros((1, nb), np.uint8)
    else:
        ker_all = np.vstack([np.zeros((1, nb), np.uint8), ker2])

    t0 = time.time()
    lights, n_total, rank = light_b_exhaustive(d2b, twod, max_b)
    out: dict = {"frame": frame, "A": a_s, "B": b_s, "axis": axis, "d": d,
                 "n_light_b_total": n_total, "n_probed": len(lights),
                 "rank_d2": rank}
    rows = []
    min_margin = None
    dips = 0
    for b, y0 in lights:
        if time.time() - t0 > budget_sec:
            out["truncated"] = True
            break
        best = None
        for zeta in ker_all:
            y = (y0 ^ zeta).astype(np.uint8)
            h = (d2cc @ y) % 2
            hp = (d2nc @ y) % 2
            c = int(h.sum() + hp.sum())
            if best is None or c < best[0]:
                best = (c, h, hp)
        _, h, hp = best
        cap = twod            # measure margins up to slack +2 (parity ladder)
        sm = slice_min(HXb, LXb, h, hp, cap)
        margin = (sm - twod) if sm is not None else None
        rows.append({"b_w": int(b.sum()), "hh": int(h.sum() + hp.sum()),
                     "slice_min": sm if sm is not None else f">{cap}",
                     "margin": margin if margin is not None else f">{cap - twod}"})
        if margin is not None:
            if min_margin is None or margin < min_margin:
                min_margin = margin
            if margin < 0:
                dips += 1
    out["min_margin"] = min_margin
    out["rung_dips"] = dips
    out["rows"] = rows[:40]
    out["t"] = round(time.time() - t0, 1)
    return out


def census_control() -> bool:
    """Doc pair: exhaustive census must contain the subset census's b's."""
    Gb0 = AbelianGroup((3, 6))
    A = Poly.from_string("x^2 + y + y^3", Gb0)
    B = Poly.from_string("1 + x + y^2", Gb0)
    Gb, chb, d2b, d2nc, d2cc = seam_split(3, 6, A, B, "x")
    lights, n_total, rank = light_b_exhaustive(d2b, 8, 10_000)
    subset_bs = set()
    nb = Gb.cardinality
    for sz in (1, 2):
        for sub in itertools.combinations(range(nb), sz):
            y0 = np.zeros(nb, np.uint8)
            for j in sub:
                y0[j] = 1
            b = (d2b @ y0) % 2
            if 0 < b.sum() < 8:
                subset_bs.add(b.tobytes())
    exh = {b.tobytes() for b, _ in lights}
    ok_sup = subset_bs <= exh
    ok_valid = all((((d2b @ y) % 2) == b).all() for b, y in lights[:50])
    print(f"census control: exhaustive {n_total} light b (rank {rank}) vs "
          f"subset {len(subset_bs)}; superset={ok_sup} preimages-valid={ok_valid}")
    return ok_sup and ok_valid


def run_exhaust(files: list[Path], out_path: Path, budget_sec: int,
                max_b: int, limit: int | None) -> None:
    assert census_control(), "census control failed"
    cells = []
    seenk = set()
    for p in files:
        for line in p.open():
            try:
                r = json.loads(line)
            except Exception:
                continue
            for a in r.get("axes", []):
                if a.get("csafe"):
                    key = (r["frame"], r["A"], r["B"], a["axis"])
                    if key not in seenk:
                        seenk.add(key)
                        cells.append((r["frame"], r["A"], r["B"], a["axis"],
                                      r["d_base"], a.get("verdict")))
    if limit:
        cells = cells[:limit]
    done = set()
    if out_path.exists():
        for line in out_path.open():
            try:
                r = json.loads(line)
                done.add((r["frame"], r["A"], r["B"], r["axis"]))
            except Exception:
                pass
    print(f"exhaustive-b probe over {len(cells)} C-safe cells "
          f"(resume-skip {len(done)})", flush=True)
    t0 = time.time()
    n_dip = 0
    margins = []
    with out_path.open("a") as fh:
        for i, (fr, a_s, b_s, axis, d, verdict) in enumerate(cells):
            if (fr, a_s, b_s, axis) in done:
                continue
            if time.time() - t0 > budget_sec:
                print("budget exhausted", flush=True)
                break
            try:
                res = probe_cell_exhaustive(fr, a_s, b_s, axis, d, max_b=max_b,
                                            budget_sec=60)
                res["hunt_verdict"] = verdict
            except Exception as e:
                res = {"frame": fr, "A": a_s, "B": b_s, "axis": axis,
                       "error": str(e)}
            fh.write(json.dumps(res) + "\n")
            fh.flush()
            mm = res.get("min_margin")
            if isinstance(mm, int):
                margins.append((mm, fr, a_s, b_s, axis))
            if isinstance(res.get("rung_dips"), int) and res["rung_dips"] > 0:
                n_dip += 1
                print(f"  RELAXED RUNG DIP: {fr} {a_s} | {b_s} {axis} "
                      f"min_margin={mm} (hunt {verdict})", flush=True)
            if (i + 1) % 20 == 0:
                print(f"  [{i+1}/{len(cells)}] {time.time()-t0:.0f}s dips={n_dip}",
                      flush=True)
    margins.sort(key=lambda t: t[0])
    print(f"done: {n_dip} dip cells; sharpest margins: {margins[:5]}", flush=True)


def run_neighbors(frame: str, a_s: str, b_s: str, budget_sec: int,
                  out_path: Path) -> None:
    """All single-monomial mutations of (A, B): full C-safe pipeline + cover
    ladder via eval_pair (a jackpot prints COUNTEREXAMPLE in the record)."""
    ell, m = (int(t) for t in frame.replace("Z", "").split("x"))
    Gb = AbelianGroup((ell, m))
    A0 = Poly.from_string(a_s, Gb)
    B0 = Poly.from_string(b_s, Gb)
    elems = [tuple(g) for g in Gb]
    cands = []
    for which, P in (("A", A0), ("B", B0)):
        supp = set(P.support)
        for old in sorted(supp):
            for new in elems:
                if tuple(new) in supp:
                    continue
                ns = (supp - {old}) | {tuple(new)}
                cands.append((which, old, tuple(new), frozenset(ns)))
    print(f"neighbors of ({a_s} | {b_s}) on {frame}: {len(cands)} mutations",
          flush=True)
    t0 = time.time()
    counters: dict[str, int] = {}
    with out_path.open("a") as fh:
        for which, old, new, ns in cands:
            if time.time() - t0 > budget_sec:
                print("budget exhausted", flush=True)
                break
            A = Poly.from_support(ns, Gb) if which == "A" else A0
            B = Poly.from_support(ns, Gb) if which == "B" else B0
            try:
                rec = eval_pair(Gb, A, B, f"nbr:{which}:{old}->{new}")
            except Exception as e:
                rec = {"stage": f"error: {e}"}
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            counters[rec.get("stage", "?")] = counters.get(rec.get("stage", "?"), 0) + 1
            for arec in rec.get("axes", []):
                v = arec.get("verdict", "?")
                counters[v] = counters.get(v, 0) + 1
                if v == "COUNTEREXAMPLE":
                    print(f"!!! COUNTEREXAMPLE CANDIDATE !!! {json.dumps(rec)}",
                          flush=True)
    print(f"neighbors done: {counters}", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["exhaust", "cell", "neighbors"])
    ap.add_argument("--files", type=str, default=None)
    ap.add_argument("--out", type=str, default=None)
    ap.add_argument("--budget-sec", type=int, default=1800)
    ap.add_argument("--max-b", type=int, default=120)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--frame", type=str)
    ap.add_argument("--A", type=str)
    ap.add_argument("--B", type=str)
    ap.add_argument("--axis", type=str, default="x")
    ap.add_argument("--d", type=int, default=None)
    args = ap.parse_args()
    if args.cmd == "exhaust":
        files = ([Path(p) for p in args.files.split(",")] if args.files
                 else sorted(CX_DIR.glob("hunt_*.jsonl")))
        out = Path(args.out) if args.out else CX_DIR / "exhaustb.jsonl"
        run_exhaust(files, out, args.budget_sec, args.max_b, args.limit)
    elif args.cmd == "cell":
        d = args.d
        if d is None:
            ell, m = (int(t) for t in args.frame.replace("Z", "").split("x"))
            Gb = AbelianGroup((ell, m))
            chb = bb_check_matrices(Poly.from_string(args.A, Gb),
                                    Poly.from_string(args.B, Gb))
            d = x_distance(chb, weight_upper_bound=12).distance
        res = probe_cell_exhaustive(args.frame, args.A, args.B, args.axis, d,
                                    max_b=args.max_b, budget_sec=args.budget_sec)
        print(json.dumps(res, indent=1))
    else:
        out = Path(args.out) if args.out else CX_DIR / "neighbors.jsonl"
        run_neighbors(args.frame, args.A, args.B, args.budget_sec, out)


if __name__ == "__main__":
    main()

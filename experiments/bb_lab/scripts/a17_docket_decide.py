"""A17: the docket decision pass — UNSAT@(floor-2) decides SF.

Phase 1 (SS6 of the A17 note) left 21 INCONCLUSIVE (cell = presentation
x axis) rows: CaDiCaL-in-pysat stalled both ways at 10M conflicts on the
floor-1 coset queries. Two sharpenings make a decision pass viable:

1. **Parity** (verified on all 21 cells; A17-P3 L1): every safe-coset
   weight is even, so the floor-1 query chased an impossible odd value.
   The decisive query is `exists coset element of weight <= floor-2`:
   SAT refutes SF outright (witness persisted); UNSAT on every G-orbit
   rep certifies `SeamCosetFloor floor` via the parity step
   (`chainWeight_coset_even` style, kernel-clean).
2. **XOR-aware solving**: the instance is 2n XOR constraints (BB rows)
   + one cardinality bound — CryptoMiniSat consumes the XORs natively
   (DIMACS `x`-lines, no Tseitin blowup). kissat/cadical binaries get
   the Tseitin CNF as second/third opinions.

Backends: `cms` (cryptominisat5), `kissat`, `cadical` (binaries on
PATH; brew-installed). Every SAT model is re-verified in numpy (elem =
seam ^ d2 f, weight <= w) before being reported — solver output is
never trusted bare. Per-query wall-clock timeout; timeouts are honest
UNKNOWNs.

Run from `experiments/bb_lab/`:
    uv run python scripts/a17_docket_decide.py --smoke
    uv run python scripts/a17_docket_decide.py --backend cms --timeout 900
    uv run python scripts/a17_docket_decide.py --summarize
"""

from __future__ import annotations

import argparse
import glob
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from pysat.card import CardEnc, EncType  # noqa: E402
from pysat.formula import IDPool  # noqa: E402

from a14_s4_ladder import orbit_reps  # noqa: E402
from a14_safe_floor_screens import (  # noqa: E402
    XCover, canonical_row, parse_poly)
from bb_lab.linalg import nullspace_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data/a17/docket_decision.jsonl"

SOLVERS = {
    "cms": ["cryptominisat5", "--verb", "0"],
    "kissat": ["kissat", "-q"],
    "cadical": ["cadical", "-q"],
}


# --------------------------------------------------------------- encoding


def encode(cov: XCover, seam: np.ndarray, w: int, xor_native: bool):
    """CNF (+ optional native XOR rows) for `exists |seam ^ d2 f| <= w`.

    Returns (clauses, xors, nv, fvar, cvar). `xors` are (lits, rhs)
    rows for DIMACS x-lines when xor_native; otherwise the XOR chains
    are Tseitin-compiled into `clauses` (same shape as
    `a14_s4_ladder.coset_query`).
    """
    nb = cov.nb
    pool = IDPool()
    fvar = [pool.id(("f", j)) for j in range(nb)]
    cvar = [pool.id(("c", i)) for i in range(2 * nb)]
    clauses: list[list[int]] = []
    xors: list[tuple[list[int], int]] = []

    for i in range(2 * nb):
        sup = np.flatnonzero(cov.d2b[i]).tolist()
        target, s = cvar[i], int(seam[i])
        if not sup:
            clauses.append([target] if s else [-target])
            continue
        if xor_native:
            # XOR(c_i, f_j...) = seam_i
            xors.append(([target] + [fvar[j] for j in sup], s))
            continue
        cur = None
        for j in sup:
            if cur is None:
                cur = fvar[j]
                continue
            t = pool.id(("x", cur, fvar[j]))
            a, b = cur, fvar[j]
            clauses.extend([[-t, a, b], [-t, -a, -b], [t, -a, b], [t, a, -b]])
            cur = t
        if s:  # c = NOT cur
            clauses.extend([[target, cur], [-target, -cur]])
        else:
            clauses.extend([[-target, cur], [target, -cur]])

    card = CardEnc.atmost(lits=cvar, bound=w, vpool=pool,
                          encoding=EncType.seqcounter)
    clauses.extend(card.clauses)
    return clauses, xors, pool.top, fvar, cvar


def write_dimacs(path: Path, clauses, xors, nv) -> None:
    with open(path, "w") as fh:
        fh.write(f"p cnf {nv} {len(clauses) + len(xors)}\n")
        for cl in clauses:
            fh.write(" ".join(map(str, cl)) + " 0\n")
        for lits, rhs in xors:
            # `x`-line asserts XOR of literals = TRUE; flip one sign for rhs=0
            lits = list(lits)
            if not rhs:
                lits[0] = -lits[0]
            fh.write("x" + " ".join(map(str, lits)) + " 0\n")


def run_query(cov: XCover, seam: np.ndarray, w: int, backend: str,
              timeout: float):
    """-> (verdict, weight|None, support|None, secs). SAT models are
    numpy-verified; a bad model raises."""
    xor_native = backend == "cms"
    clauses, xors, nv, fvar, cvar = encode(cov, seam, w, xor_native)
    t0 = time.time()
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
        cnf_path = Path(fh.name)
    try:
        write_dimacs(cnf_path, clauses, xors, nv)
        try:
            proc = subprocess.run(
                SOLVERS[backend] + [str(cnf_path)],
                capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "UNKNOWN", None, None, round(time.time() - t0, 1)
        out = proc.stdout
        if proc.returncode == 20 or "\ns UNSATISFIABLE" in "\n" + out:
            return "UNSAT", None, None, round(time.time() - t0, 1)
        if proc.returncode != 10 and "\ns SATISFIABLE" not in "\n" + out:
            raise RuntimeError(
                f"{backend} rc={proc.returncode}: {out[-300:]}\n"
                f"{proc.stderr[-300:]}")
        pos = set()
        for line in out.splitlines():
            if line.startswith("v"):
                for tok in line[1:].split():
                    v = int(tok)
                    if v > 0:
                        pos.add(v)
        f = np.array([1 if fv in pos else 0 for fv in fvar], dtype=np.uint8)
        elem = seam ^ ((cov.d2b @ f) & 1)
        wt = int(elem.sum())
        assert wt <= w, f"model violates bound: {wt} > {w}"
        return "SAT", wt, np.flatnonzero(elem).tolist(), \
            round(time.time() - t0, 1)
    finally:
        cnf_path.unlink(missing_ok=True)


# ----------------------------------------------------------------- docket


def load_cells() -> list[dict]:
    seen: dict[tuple, dict] = {}
    for p in sorted(glob.glob(str(ROOT / "data/a17/corpus_battery*.jsonl"))):
        for line in open(p):
            r = json.loads(line)
            seen.setdefault((r["instance_id"], r["axis"]), r)
    inc = [r for r in seen.values() if r["status"] == "INCONCLUSIVE"]
    return sorted(inc, key=lambda r: (r["n"], r["instance_id"], r["axis"]))


def decide_cell(r: dict, backend: str, timeout: float) -> dict:
    A, B = parse_poly(r["A"]), parse_poly(r["B"])
    Ac, Bc, lc, mc = canonical_row(A, B, r["ell"], r["m"], r["axis"])
    cov = XCover(Ac, Bc, lc, mc)
    reps = orbit_reps(cov, nullspace_f2(cov.d2b))
    w = r["floor"] - 2  # parity-decisive bound
    rec = {"instance_id": r["instance_id"], "axis": r["axis"],
           "group": r["group"], "n": r["n"], "k": r["k"],
           "d_base": r["d_base"], "floor": r["floor"], "w_query": w,
           "backend": backend, "A": r["A"], "B": r["B"], "reps": []}
    for i, z in enumerate(reps):
        v, wt, sup, secs = run_query(cov, cov.seam(z), w, backend, timeout)
        rrec = {"rep": i, "verdict": v, "secs": secs}
        if wt is not None:
            rrec["weight"], rrec["witness_support"] = wt, sup
        rec["reps"].append(rrec)
        print(f"    rep {i + 1}/{len(reps)}: {v}"
              + (f" (wt {wt})" if wt else "") + f" [{secs}s]", flush=True)
        if v == "SAT":
            break
    vs = [x["verdict"] for x in rec["reps"]]
    rec["status"] = ("SF-REFUTED" if "SAT" in vs
                     else "SF-CERTIFIED" if all(v == "UNSAT" for v in vs)
                     else "UNKNOWN")
    return rec


# ------------------------------------------------------------------ modes


def smoke(backend: str, timeout: float) -> bool:
    """SAT sanity on a known-refuted cell; UNSAT sanity on pair72-base."""
    ok = True
    cells = {(r["instance_id"], r["axis"]): r for p in
             glob.glob(str(ROOT / "data/a17/corpus_battery*.jsonl"))
             for r in map(json.loads, open(p))}
    refuted = next(r for r in cells.values()
                   if r["status"] == "SF-REFUTED" and r["d_base"] == 8
                   and any(v.get("weight", 99) <= 14
                           for v in r["s4"]["verdicts"]))
    print(f"smoke 1 (expect SAT<=14): {refuted['instance_id']}:"
          f"{refuted['axis']} [{refuted['group']}]")
    A, B = parse_poly(refuted["A"]), parse_poly(refuted["B"])
    Ac, Bc, lc, mc = canonical_row(A, B, refuted["ell"], refuted["m"],
                                   refuted["axis"])
    cov = XCover(Ac, Bc, lc, mc)
    reps = orbit_reps(cov, nullspace_f2(cov.d2b))
    hit = False
    for z in reps:
        v, wt, _, secs = run_query(cov, cov.seam(z), 14, backend, timeout)
        print(f"    {v}" + (f" wt {wt}" if wt else "") + f" [{secs}s]")
        if v == "SAT":
            hit = True
            break
    ok &= hit

    print("smoke 2 (expect UNSAT@6): pair72-base [[36,4,4]] x, floor 8")
    A, B = parse_poly("x^2 + y + y^3"), parse_poly("1 + x + y^2")
    cov = XCover(A, B, 3, 6)
    reps = orbit_reps(cov, nullspace_f2(cov.d2b))
    for z in reps:
        v, wt, _, secs = run_query(cov, cov.seam(z), 6, backend, timeout)
        print(f"    {v}" + (f" wt {wt}" if wt else "") + f" [{secs}s]")
        ok &= v == "UNSAT"
    print(f"SMOKE {'PASS' if ok else 'FAIL'} ({backend})")
    return ok


def summarize() -> None:
    rows = [json.loads(line) for line in open(OUT)]
    best: dict[tuple, dict] = {}
    for r in rows:  # later runs (stronger backends) override
        best[(r["instance_id"], r["axis"])] = r
    from collections import Counter
    print(Counter(r["status"] for r in best.values()))
    for r in sorted(best.values(), key=lambda r: r["status"]):
        wits = [x for x in r["reps"] if x.get("weight")]
        print(f"  {r['instance_id']}:{r['axis']} [{r['group']}] "
              f"floor {r['floor']} -> {r['status']}"
              + (f" wt={min(x['weight'] for x in wits)}" if wits else "")
              + f" ({r['backend']})")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend", default="cms", choices=list(SOLVERS))
    ap.add_argument("--timeout", type=float, default=900.0)
    ap.add_argument("--shard", default=None, help="K/N over docket cells")
    ap.add_argument("--only", default=None,
                    help="instance_id:axis (comma-separated) filter")
    ap.add_argument("--redo", action="store_true",
                    help="re-run cells already decided in the out file")
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize", action="store_true")
    args = ap.parse_args()

    if args.smoke:
        sys.exit(0 if smoke(args.backend, args.timeout) else 1)
    if args.summarize:
        summarize()
        return

    cells = load_cells()
    if args.only:
        keys = {tuple(t.split(":")) for t in args.only.split(",")}
        cells = [r for r in cells if (r["instance_id"], r["axis"]) in keys]
    if args.shard:
        k, n = (int(t) for t in args.shard.split("/"))
        cells = cells[k::n]
    if not args.redo and OUT.exists():
        done = {(json.loads(line)["instance_id"], json.loads(line)["axis"])
                for line in open(OUT)
                if json.loads(line)["status"] != "UNKNOWN"}
        cells = [r for r in cells
                 if (r["instance_id"], r["axis"]) not in done]
    print(f"{len(cells)} docket cells to decide "
          f"(backend {args.backend}, timeout {args.timeout}s)", flush=True)
    t0 = time.time()
    for i, r in enumerate(cells):
        print(f"== [{i + 1}/{len(cells)}] {r['instance_id']}:{r['axis']} "
              f"[{r['group']}] [[{r['n']},{r['k']},{r['d_base']}]] "
              f"w<={r['floor'] - 2} ==", flush=True)
        rec = decide_cell(r, args.backend, args.timeout)
        with open(OUT, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        marker = {"SF-CERTIFIED": "*** CERTIFIED ***",
                  "SF-REFUTED": "refuted",
                  "UNKNOWN": "unknown"}[rec["status"]]
        print(f"  -> {marker}  [{time.time() - t0:.0f}s total]", flush=True)
    print("pass complete", flush=True)


if __name__ == "__main__":
    main()

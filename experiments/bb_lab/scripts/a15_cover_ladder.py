"""A15: cover-side ladders for the 18 SF-certified cells.

SF-certification (SS6.1) bounds the SAFE sector of the double cover;
the doubling verdict still owes the cover's actual X-distance — which
also decides the dangerous ((M)-half) sector. Per certified
(code, axis), on the cover BB code (2l, m) resp. (l, 2m):

  * **witness phase**: one SAT call at w = 2d (16): an explicit cover
    logical of weight <= 16. Expected weight exactly 16 (the lift of a
    weight-8 base logical); a verified witness of weight < 16 would
    REFUTE the doubling for that cell (a light dangerous-sector
    logical — SF does not exclude it).
  * **unsat phase**: one decisive call at w = 2d - 2 (14): |A|, |B|
    odd forces every element of ker H_Z to even weight (augmentation
    hom per block: eps(v_a) = eps(v_b)), so UNSAT@14 <=> UNSAT@15,
    and with the witness this pins **d_X(cover) = 16 exactly**.

House convention (matches `bb-lab fill-distances` and SSSS13-14): all
distances are d_X. The Z-side of a BB pair is the X-side of the
reversed pair (M_A^T = M_{A-bar}); full-d packaging handles it via
that symmetry, out of scope here.

Backends: witness = pysat CaDiCaL (in-process, fast SAT-side);
unsat = cryptominisat5 with H_Z rows + logical-overlap definitions as
native DIMACS x-lines (the SS6.1 unlock), kissat/cadical CNF fallback.
Witnesses are numpy-verified (syndrome, odd logical overlap, weight,
parity) before being reported.

Smoke (both phases, known truth): pair72-base [[36,4,4]] x-cover =
[[72,4,8]]: witness@8 -> SAT wt 8, UNSAT@6.

Run from `experiments/bb_lab/`:
    uv run python scripts/a15_cover_ladder.py --smoke
    uv run python scripts/a15_cover_ladder.py --phase witness
    uv run python scripts/a15_cover_ladder.py --phase unsat --shard 0/4
    uv run python scripts/a15_cover_ladder.py --summarize
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
from pysat.formula import CNF, IDPool  # noqa: E402
from pysat.solvers import Cadical195  # noqa: E402

from bb_lab.checks import CheckMatrices, bb_check_matrices  # noqa: E402
from bb_lab.group import AbelianGroup  # noqa: E402
from bb_lab.poly import Poly  # noqa: E402
from bb_lab.sat_distance import find_logical_z  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT_WITNESS = ROOT / "data/a15/cover_witness.jsonl"
OUT_UNSAT = ROOT / "data/a15/cover_unsat14.jsonl"

SOLVERS = {
    "cms": ["cryptominisat5", "--verb", "0"],
    "kissat": ["kissat", "-q"],
    "cadical": ["cadical", "-q"],
}


def cover_checks(A_str: str, B_str: str, l: int, m: int,
                 axis: str) -> CheckMatrices:
    dims = (2 * l, m) if axis == "x" else (l, 2 * m)
    G = AbelianGroup(dims)
    A, B = Poly.from_string(A_str, G), Poly.from_string(B_str, G)
    assert len(A.support) == 3 and len(B.support) == 3, \
        "parity argument needs odd |A|, |B|"
    return bb_check_matrices(A, B)


def verify_witness(checks: CheckMatrices, L_Z: np.ndarray,
                   v: np.ndarray, w: int) -> int:
    """Numpy re-verification; returns the weight. Raises on any failure."""
    wt = int(v.sum())
    assert 0 < wt <= w, f"weight {wt} outside (0, {w}]"
    assert wt % 2 == 0, f"odd-weight element {wt} contradicts parity"
    assert not ((checks.H_Z @ v) % 2).any(), "witness has nonzero syndrome"
    assert ((L_Z @ v) % 2).any(), "witness commutes with all logicals"
    return wt


# ------------------------------------------------------- witness (SAT@2d)


def witness_query(checks: CheckMatrices, w: int):
    """pysat CaDiCaL: cover logical of weight <= w. -> (wt, support)|None."""
    from bb_lab.sat_distance import _build_cnf_at_weight
    L_Z = find_logical_z(checks)
    cnf, qubit_vars = _build_cnf_at_weight(checks.H_Z, L_Z, w)
    solver = Cadical195(bootstrap_with=cnf.clauses)
    try:
        if not solver.solve():
            return None
        truth = {abs(lit): lit > 0 for lit in solver.get_model()}
        v = np.array([1 if truth.get(qv, False) else 0 for qv in qubit_vars],
                     dtype=np.uint8)
        wt = verify_witness(checks, L_Z, v, w)
        return wt, np.flatnonzero(v).tolist()
    finally:
        solver.delete()


# ------------------------------------------------- unsat (CMS x-lines @14)


def unsat_query(checks: CheckMatrices, w: int, backend: str,
                timeout: float):
    """Decisive cover query at w: -> (verdict, wt|None, support|None, secs).

    cms: H_Z rows and per-logical overlap definitions as native x-lines;
    kissat/cadical: Tseitin CNF of the same formula.
    """
    L_Z = find_logical_z(checks)
    n = checks.num_qubits
    pool = IDPool()
    qv = [pool.id(("q", j)) for j in range(n)]
    clauses: list[list[int]] = []
    xors: list[list[int]] = []  # each: literal list, asserted XOR = TRUE

    def xor_zero(lits: list[int]) -> None:
        lits = list(lits)
        lits[0] = -lits[0]  # XOR(lits) = FALSE
        xors.append(lits)

    def tseitin_chain(idx: list[int]) -> int:
        acc = qv[idx[0]]
        for j in idx[1:]:
            t = pool.id(("t", acc, j))
            a, b = acc, qv[j]
            clauses.extend([[-t, -a, -b], [-t, a, b], [t, -a, b], [t, a, -b]])
            acc = t
        return acc

    native = backend == "cms"
    for row in checks.H_Z:
        idx = np.flatnonzero(row).tolist()
        if not idx:
            continue
        if native:
            xor_zero([qv[j] for j in idx])
        else:
            clauses.append([-tseitin_chain(idx)])
    outs = []
    for L in L_Z:
        idx = np.flatnonzero(L).tolist()
        if not idx:
            continue
        if native:
            o = pool.id(("o", len(outs)))
            xor_zero([o] + [qv[j] for j in idx])  # o = XOR(supp)
            outs.append(o)
        else:
            outs.append(tseitin_chain(idx))
    clauses.append(outs)  # some logical overlap is odd
    card = CardEnc.atmost(lits=qv, bound=w, vpool=pool,
                          encoding=EncType.seqcounter)
    clauses.extend(card.clauses)

    t0 = time.time()
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
        path = Path(fh.name)
    try:
        with open(path, "w") as fh:
            fh.write(f"p cnf {pool.top} {len(clauses) + len(xors)}\n")
            for cl in clauses:
                fh.write(" ".join(map(str, cl)) + " 0\n")
            for lits in xors:
                fh.write("x" + " ".join(map(str, lits)) + " 0\n")
        try:
            proc = subprocess.run(SOLVERS[backend] + [str(path)],
                                  capture_output=True, text=True,
                                  timeout=timeout)
        except subprocess.TimeoutExpired:
            return "UNKNOWN", None, None, round(time.time() - t0, 1)
        secs = round(time.time() - t0, 1)
        out = proc.stdout
        if proc.returncode == 20 or "\ns UNSATISFIABLE" in "\n" + out:
            return "UNSAT", None, None, secs
        if proc.returncode != 10 and "\ns SATISFIABLE" not in "\n" + out:
            raise RuntimeError(f"{backend} rc={proc.returncode}: "
                               f"{out[-200:]} {proc.stderr[-200:]}")
        pos = {int(t) for line in out.splitlines() if line.startswith("v")
               for t in line[1:].split() if int(t) > 0}
        v = np.array([1 if x in pos else 0 for x in qv], dtype=np.uint8)
        wt = verify_witness(checks, L_Z, v, w)
        return "SAT", wt, np.flatnonzero(v).tolist(), secs
    finally:
        path.unlink(missing_ok=True)


# ------------------------------------------------------------------ cells


def certified_cells() -> list[dict]:
    battery = {}
    for p in sorted(glob.glob(str(ROOT / "data/a15/corpus_battery*.jsonl"))):
        for r in map(json.loads, open(p)):
            battery.setdefault((r["instance_id"], r["axis"]), r)
    best: dict[tuple, dict] = {}
    for line in open(ROOT / "data/a15/docket_decision.jsonl"):
        r = json.loads(line)
        key = (r["instance_id"], r["axis"])
        best[key] = {**battery[key], **r}  # battery carries ell/m
    cells = [r for r in best.values() if r["status"] == "SF-CERTIFIED"]
    return sorted(cells, key=lambda r: (r["n"], r["instance_id"], r["axis"]))


def load_done(path: Path) -> set[tuple]:
    if not path.exists():
        return set()
    return {(j["instance_id"], j["axis"])
            for j in map(json.loads, open(path))}


def run_witness(cells: list[dict]) -> None:
    done = load_done(OUT_WITNESS)
    todo = [r for r in cells if (r["instance_id"], r["axis"]) not in done]
    print(f"witness phase: {len(todo)} cells", flush=True)
    for r in todo:
        t0 = time.time()
        checks = cover_checks(r["A"], r["B"], r["ell"], r["m"], r["axis"])
        res = witness_query(checks, 2 * r["d_base"])
        rec = {"instance_id": r["instance_id"], "axis": r["axis"],
               "group": r["group"], "d_base": r["d_base"],
               "cover_n": checks.num_qubits,
               "secs": round(time.time() - t0, 1)}
        if res is None:
            rec["status"] = "NO-WITNESS<=2d (!!)"  # would exceed 2d bound
        else:
            wt, sup = res
            rec.update({"weight": wt, "witness_support": sup,
                        "status": ("WITNESS-AT-2d" if wt == 2 * r["d_base"]
                                   else "LIGHT-WITNESS (doubling refuted)")})
        with open(OUT_WITNESS, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(f"  {r['instance_id'][:8]}:{r['axis']} [[{rec['cover_n']},"
              f"{r['k']},?]]: {rec['status']}"
              + (f" wt={rec.get('weight')}" if "weight" in rec else "")
              + f" [{rec['secs']}s]", flush=True)


def run_unsat(cells: list[dict], backend: str, timeout: float,
              shard: str | None) -> None:
    if shard:
        k, n = (int(t) for t in shard.split("/"))
        cells = cells[k::n]
    done = load_done(OUT_UNSAT)
    todo = [r for r in cells if (r["instance_id"], r["axis"]) not in done]
    print(f"unsat phase: {len(todo)} cells (backend {backend}, "
          f"timeout {timeout}s)", flush=True)
    for r in todo:
        checks = cover_checks(r["A"], r["B"], r["ell"], r["m"], r["axis"])
        w = 2 * r["d_base"] - 2
        v, wt, sup, secs = unsat_query(checks, w, backend, timeout)
        rec = {"instance_id": r["instance_id"], "axis": r["axis"],
               "group": r["group"], "d_base": r["d_base"],
               "cover_n": checks.num_qubits, "w_query": w,
               "backend": backend, "verdict": v, "secs": secs}
        if v == "UNSAT":
            rec["status"] = "DX-CONFIRMED-2d"
        elif v == "SAT":
            rec.update({"weight": wt, "witness_support": sup,
                        "status": "DOUBLING-REFUTED (light cover logical)"})
        else:
            rec["status"] = "UNKNOWN (timeout)"
        with open(OUT_UNSAT, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(f"  {r['instance_id'][:8]}:{r['axis']} "
              f"[[{rec['cover_n']}]] w<={w}: {rec['status']} [{secs}s]",
              flush=True)


def smoke(backend: str) -> bool:
    print("smoke: pair72-base [[36,4,4]] x-cover = [[72,4,8]]")
    checks = cover_checks("x^2 + y + y^3", "1 + x + y^2", 3, 6, "x")
    res = witness_query(checks, 8)
    ok = res is not None and res[0] == 8
    print(f"  witness@8: {res[0] if res else None} "
          f"{'OK' if ok else 'FAIL'}")
    v, wt, _, secs = unsat_query(checks, 6, backend, 300)
    ok2 = v == "UNSAT"
    print(f"  unsat@6 ({backend}): {v} [{secs}s] {'OK' if ok2 else 'FAIL'}")
    print(f"SMOKE {'PASS' if ok and ok2 else 'FAIL'}")
    return ok and ok2


def summarize() -> None:
    wit = {(j["instance_id"], j["axis"]): j
           for j in map(json.loads, open(OUT_WITNESS))} \
        if OUT_WITNESS.exists() else {}
    uns = {(j["instance_id"], j["axis"]): j
           for j in map(json.loads, open(OUT_UNSAT))} \
        if OUT_UNSAT.exists() else {}
    for r in certified_cells():
        key = (r["instance_id"], r["axis"])
        wrec, urec = wit.get(key), uns.get(key)
        wpart = (f"wit={wrec['weight']}" if wrec and "weight" in wrec
                 else wrec["status"] if wrec else "wit=?")
        upart = urec["status"] if urec else "unsat14=?"
        confirmed = (wrec and wrec.get("weight") == 2 * r["d_base"]
                     and urec and urec["status"] == "DX-CONFIRMED-2d")
        mark = " *** d_X(cover) = 2d CONFIRMED ***" if confirmed else ""
        print(f"  {r['instance_id'][:8]}:{r['axis']} [{r['group']}] "
              f"-> {wpart}, {upart}{mark}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--phase", choices=["witness", "unsat", "both"],
                    default="both")
    ap.add_argument("--backend", default="cms", choices=list(SOLVERS))
    ap.add_argument("--timeout", type=float, default=14400.0)
    ap.add_argument("--shard", default=None)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize", action="store_true")
    args = ap.parse_args()

    if args.smoke:
        sys.exit(0 if smoke(args.backend) else 1)
    if args.summarize:
        summarize()
        return
    cells = certified_cells()
    print(f"{len(cells)} certified cells", flush=True)
    if args.phase in ("witness", "both"):
        run_witness(cells)
    if args.phase in ("unsat", "both"):
        run_unsat(cells, args.backend, args.timeout, args.shard)


if __name__ == "__main__":
    main()

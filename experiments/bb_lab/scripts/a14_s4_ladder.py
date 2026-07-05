"""A14 S4: budgeted per-class coset-minimum SAT (witness side + certify side).

For a safe class [seamC(zeta)] the query "exists element of weight <= w in
the coset seam + im d2?" is one SAT call: f-variables (base 2-chain),
c-variables (output cells, XOR-linked to f through the d2 row supports),
and a cardinality bound.  SAT at w = floor-1 refutes the safe floor with
an explicit certificate (S4-reject); UNSAT at floor-1 for *every*
G-orbit representative CERTIFIES `SeamCosetFloor floor` (solver-grade) —
orbit reps suffice by Prop A14.1(4).

Runs:
1. validation on 12 Phase-1 gap rows (exact minima known: decision at
   floor-1 must be SAT exactly when the exact minimum is below floor);
2. gross-x (proven SF-true in Lean): expect UNSAT on all orbit reps —
   an independent SAT-vs-Lean cross-check of the MIm floor;
3. hit3/4/6-y (the [[144,12,12]] engine targets): decide their safe
   floors outright (36-cell base, cheap);
4. bb_288-y (the open anti-instance axis): budgeted attempt, honest
   unknown on budget exhaustion.

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_s4_ladder.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from pysat.card import CardEnc, EncType  # noqa: E402
from pysat.formula import IDPool  # noqa: E402
from pysat.solvers import Cadical153  # noqa: E402

from a14_safe_floor_screens import XCover, canonical_row, parse_poly  # noqa: E402
from bb_lab.linalg import nullspace_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


def coset_query(cov: XCover, seam: np.ndarray, w: int,
                conf_budget: int = 3_000_000):
    """SAT: exists f with |seam ^ d2 f| <= w?  -> (verdict, weight|None).

    verdict in {"SAT", "UNSAT", "UNKNOWN"}; on SAT the achieved weight of
    the extracted (verified) coset element is returned.
    """
    nb = cov.nb
    pool = IDPool()
    fvar = [pool.id(("f", j)) for j in range(nb)]
    cvar = [pool.id(("c", i)) for i in range(2 * nb)]
    clauses = []

    def xor_pair(a: int, b: int) -> int:
        t = pool.id(("x", a, b))
        clauses.extend([[-t, a, b], [-t, -a, -b], [t, -a, b], [t, a, -b]])
        return t

    for i in range(2 * nb):
        sup = np.flatnonzero(cov.d2b[i]).tolist()
        cur = None
        for j in sup:
            cur = fvar[j] if cur is None else xor_pair(cur, fvar[j])
        target = cvar[i]
        if cur is None:  # empty row: c_i = seam_i
            clauses.append([target] if seam[i] else [-target])
            continue
        if seam[i]:  # c = NOT cur
            clauses.extend([[target, cur], [-target, -cur]])
        else:        # c = cur
            clauses.extend([[-target, cur], [target, -cur]])

    card = CardEnc.atmost(lits=cvar, bound=w, vpool=pool,
                          encoding=EncType.seqcounter)
    with Cadical153(bootstrap_with=clauses + card.clauses) as solver:
        solver.conf_budget(conf_budget)
        res = solver.solve_limited()
        if res is None:
            return "UNKNOWN", None
        if not res:
            return "UNSAT", None
        model = set(solver.get_model())
        f = np.array([1 if fvar[j] in model else 0 for j in range(nb)],
                     dtype=np.uint8)
        elem = seam ^ ((cov.d2b @ f) & 1)
        wt = int(elem.sum())
        assert wt <= w, "extracted certificate exceeds the bound"
        return "SAT", wt


def orbit_reps(cov: XCover, ker: np.ndarray) -> list[np.ndarray]:
    """G-translation orbit representatives of ker d2 \\ 0 (A14.1(4))."""
    kappa = ker.shape[0]
    elems = {}
    for bits in range(1, 1 << kappa):
        z = np.zeros(cov.nb, dtype=np.uint8)
        for i in range(kappa):
            if (bits >> i) & 1:
                z ^= ker[i]
        elems[z.tobytes()] = z
    seen, reps = set(), []
    for key, z in elems.items():
        if key in seen:
            continue
        reps.append(z)
        for gx in range(cov.l):
            for gy in range(cov.m):
                t = np.zeros_like(z)
                for x in range(cov.l):
                    for y in range(cov.m):
                        t[((x + gx) % cov.l) * cov.m + (y + gy) % cov.m] = \
                            z[x * cov.m + y]
                seen.add(t.tobytes())
    return reps


def run_target(name, As, Bs, l, m, axis, d_base, conf_budget=3_000_000):
    Ac, Bc, lc, mc = canonical_row(parse_poly(As), parse_poly(Bs), l, m, axis)
    cov = XCover(Ac, Bc, lc, mc)
    ker = nullspace_f2(cov.d2b)
    reps = orbit_reps(cov, ker)
    floor = 2 * d_base
    verdicts = []
    t0 = time.time()
    for i, z in enumerate(reps):
        v, wt = coset_query(cov, cov.seam(z), floor - 1, conf_budget)
        verdicts.append({"rep": i, "verdict": v, "weight": wt})
        print(f"  {name} rep {i + 1}/{len(reps)}: {v}"
              + (f" (weight {wt})" if wt is not None else "")
              + f"  [{time.time() - t0:.0f}s]")
        if v == "SAT":
            break  # one light class refutes SF; no need to continue
    status = ("SF-REFUTED" if any(r["verdict"] == "SAT" for r in verdicts)
              else "SF-CERTIFIED" if all(r["verdict"] == "UNSAT"
                                         for r in verdicts)
              else "INCONCLUSIVE")
    print(f"  {name}: {status} (floor {floor}, {len(reps)} orbit reps)")
    return {"name": name, "floor": floor, "n_orbit_reps": len(reps),
            "verdicts": verdicts, "status": status}


def main() -> None:
    print("== S4 validation on 12 Phase-1 gap rows (exact GT known) ==")
    gap = [json.loads(line)
           for line in open(ROOT / "data/a14/phase2_gap_rows.jsonl")]
    rng = np.random.default_rng(14)
    ok = True
    for r in [gap[int(i)] for i in rng.choice(len(gap), 12, replace=False)]:
        Ac, Bc, lc, mc = canonical_row(parse_poly(r["A"]), parse_poly(r["B"]),
                                       r["ell"], r["m"], r["axis"])
        cov = XCover(Ac, Bc, lc, mc)
        ker = nullspace_f2(cov.d2b)
        floor = 2 * r["d_base"]
        for bits_i in range(min(3, (1 << ker.shape[0]) - 1)):
            bits = bits_i + 1
            z = np.zeros(cov.nb, dtype=np.uint8)
            for i in range(ker.shape[0]):
                if (bits >> i) & 1:
                    z ^= ker[i]
            v, wt = coset_query(cov, cov.seam(z), floor - 1)
            exact = r["exact_minima"][bits - 1]
            expect = "SAT" if exact < floor else "UNSAT"
            if v != expect or (wt is not None and wt < exact):
                ok = False
                print(f"  MISMATCH {r['instance_id']}:{r['axis']} class "
                      f"{bits}: sat={v} wt={wt} exact={exact}")
    print(f"  validation: {'PASS' if ok else 'FAIL'}")

    print("\n== proof-grade cross-check: gross-x (Lean says SF-true) ==")
    results = [run_target("gross-x", "x^3 + y + y^2", "y^3 + x + x^2",
                          6, 6, "x", 6)]
    ok = ok and results[0]["status"] == "SF-CERTIFIED"

    print("\n== engine targets: hit3/4/6 y-covers (floor 12) ==")
    for name, Bs in [("hit3-y", "y + x*y^2 + x^2"),
                     ("hit4-y", "y^2 + x*y^3 + x^2*y"),
                     ("hit6-y", "x*y + x^2*y^2 + x^3")]:
        results.append(run_target(name, "y^3 + x + x^2", Bs, 6, 6, "y", 6))

    print("\n== bb_288-y (open axis; budgeted) ==")
    results.append(run_target("bb288-y", "x^3 + y^2 + y^7", "y^3 + x + x^2",
                              12, 12, "y", 18, conf_budget=10_000_000))

    with open(ROOT / "data/a14/s4_results.json", "w") as fh:
        json.dump(results, fh, indent=1)
    print(f"\n{'S4 PASS' if ok else 'S4 FAILED'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()

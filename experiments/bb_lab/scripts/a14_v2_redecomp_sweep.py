"""A14 v2 hunt: re-decomposition + bb_288 presentation orbits.

Two sweeps the §15 v1 orbit deliberately left out:

**Hunt A — bb_108 on Z18xZ3.** The abstract group Z9xZ6 is also Z18xZ3;
the change of coordinates phi(a,b) = ((10a+9b) mod 18, b mod 3) splices
the Z2 of y onto the Z9 of x, so the two cyclic axes — and hence the
literal-lift doublings — are genuinely different covers (the
tour-de-gross mixed-lift kind).  Transformed supports:
A' = u^12 + u^9 v + v^2, B' = u^2 + u^9 + u^10.  Both axes, v1-style
equivalence set (doubled-axis translations x diagonal units x swap),
floor 20.

**Hunt B — bb_288 [[288,12,18]] on Z12xZ12.** Route (b) proper: the
stored presentation fails the safe floor on both axes (§11); this
sweeps its presentation orbit at floor 36.  An SF-certified cell here
would point at [[576,12,36]].

Staged battery per cell, reordered for scale: S0 with early exit
(first light seam rejects; no k-gate needed for soundness of a reject
— a k-jumping cell is dead anyway and a k-preserving one's raw seam is
a genuine coset element) -> k-gate on S0 survivors -> S1+/S2 -> S4 ->
(Hunt A only) cover distance ladder.  Hunt B certified cells are
flagged for a dedicated distance job (n = 576 ladders are out of scope).

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_v2_redecomp_sweep.py
"""

from __future__ import annotations

import itertools
import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from a14_safe_floor_screens import XCover, canonical_row, h1_dim  # noqa: E402
from a14_phase2_screens import screen_row_phase2  # noqa: E402
from a14_s4_ladder import run_target  # noqa: E402
from bb_lab.linalg import nullspace_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
FINALIST_CAP = 24


def units(n: int) -> list[int]:
    return [u for u in range(1, n) if np.gcd(u, n) == 1]


def poly_str(sup) -> str:
    terms = []
    for (e, f) in sorted(sup):
        t = []
        if e:
            t.append(f"x^{e}" if e > 1 else "x")
        if f:
            t.append(f"y^{f}" if f > 1 else "y")
        terms.append("*".join(t) if t else "1")
    return " + ".join(terms)


# ---- Hunt A setup: bb_108 recoordinatized on Z18xZ3 ------------------------

A108 = [(3, 0), (0, 1), (0, 2)]
B108 = [(0, 3), (1, 0), (2, 0)]


def phi(a: int, b: int) -> tuple[int, int]:
    return ((10 * a + 9 * b) % 18, b % 3)


assert len({phi(a, b) for a in range(9) for b in range(6)}) == 54
A108_18 = sorted(phi(a, b) for (a, b) in A108)
B108_18 = sorted(phi(a, b) for (a, b) in B108)


# ---------------------------------------------------------------- the sweep


def s0_early(cov: XCover, floor: int):
    """Raw seam minimum with early exit below the floor."""
    ker = nullspace_f2(cov.d2b)
    kappa = ker.shape[0]
    worst = None
    for bits in range(1, 1 << kappa):
        z = np.zeros(cov.nb, dtype=np.uint8)
        for i in range(kappa):
            if (bits >> i) & 1:
                z ^= ker[i]
        w = int(cov.seam(z).sum())
        worst = w if worst is None else min(worst, w)
        if w < floor:
            return worst, False
    return worst, True


def sweep(hunt: str, A0, B0, l, m, d_base, run_ladder: bool):
    floor = 2 * d_base
    out = {"hunt": hunt, "l": l, "m": m, "floor": floor, "axes": {}}
    finalists = []
    t0 = time.time()
    for axis in ("x", "y"):
        shifts = range(l) if axis == "x" else range(m)
        seen, cells = set(), []
        for u, v, swap in itertools.product(units(l), units(m), (False, True)):
            Au = {((u * e) % l, (v * f) % m) for (e, f) in A0}
            Bu = {((u * e) % l, (v * f) % m) for (e, f) in B0}
            if swap:
                Au, Bu = Bu, Au
            for ta, tb in itertools.product(shifts, shifts):
                if axis == "x":
                    A2 = frozenset(((e + ta) % l, f) for (e, f) in Au)
                    B2 = frozenset(((e + tb) % l, f) for (e, f) in Bu)
                else:
                    A2 = frozenset((e, (f + ta) % m) for (e, f) in Au)
                    B2 = frozenset((e, (f + tb) % m) for (e, f) in Bu)
                if (A2, B2) not in seen:
                    seen.add((A2, B2))
                    cells.append((sorted(A2), sorted(B2)))
        print(f"== {hunt} axis {axis}: {len(cells)} cells ==", flush=True)
        s0_hist, s0_pass, kgate_fail = Counter(), [], 0
        for i, (A, B) in enumerate(cells):
            Ac, Bc, lc, mc = canonical_row(A, B, l, m, axis)
            cov = XCover(Ac, Bc, lc, mc)
            s0min, passed = s0_early(cov, floor)
            s0_hist[s0min] += 1
            if not passed:
                continue
            # lazy k-gate, only for S0 survivors
            if h1_dim(cov.d2c, cov.d1c) != h1_dim(cov.d2b, cov.d1b):
                kgate_fail += 1
                continue
            s0_pass.append((A, B))
            if (i + 1) % 1000 == 0:
                print(f"  ... {i + 1}/{len(cells)} ({time.time() - t0:.0f}s)",
                      flush=True)
        print(f"  axis {axis}: S0 histogram {dict(sorted(s0_hist.items()))}; "
              f"S0+k survivors {len(s0_pass)} "
              f"(k-gate killed {kgate_fail} S0 survivors)", flush=True)
        out["axes"][axis] = {"cells": len(cells),
                             "s0_hist": dict(s0_hist),
                             "survivors": len(s0_pass)}
        for A, B in s0_pass[:]:
            r2 = screen_row_phase2(A, B, l, m, axis, d_base)
            if not r2["reject"]:
                finalists.append({"axis": axis, "A": poly_str(A),
                                  "B": poly_str(B),
                                  "cheap_min": r2["min_reached"]})
                print(f"  CHEAP-TIER PASS: axis {axis}, A = {poly_str(A)}, "
                      f"B = {poly_str(B)} (min {r2['min_reached']})",
                      flush=True)

    print(f"\n== {hunt}: S4 on {len(finalists)} finalists ==", flush=True)
    if len(finalists) > FINALIST_CAP:
        print(f"  (capped at {FINALIST_CAP}; {len(finalists) - FINALIST_CAP} "
              f"deferred)", flush=True)
    for rec in finalists[:FINALIST_CAP]:
        s4 = run_target(f"{hunt}-{rec['axis']}", rec["A"], rec["B"],
                        l, m, rec["axis"], d_base, conf_budget=10_000_000)
        rec["s4_status"] = s4["status"]
        if s4["status"] == "SF-CERTIFIED":
            print(f"  *** {hunt} SF-CERTIFIED at axis {rec['axis']}: "
                  f"A = {rec['A']}, B = {rec['B']}", flush=True)
            if run_ladder:
                from a14_d10_battery import cover_distance_ladder
                rec["cover"] = cover_distance_ladder(
                    hunt, rec["A"], rec["B"], l, m, rec["axis"], floor)
            else:
                print("  (distance ladder deferred — dedicated job)",
                      flush=True)
    out["finalists"] = finalists
    print(f"{hunt} done ({time.time() - t0:.0f}s)\n", flush=True)
    return out


def main() -> None:
    results = [
        sweep("bb108@Z18xZ3", A108_18, B108_18, 18, 3, 10, run_ladder=True),
        sweep("bb288@Z12xZ12",
              [(3, 0), (0, 2), (0, 7)], [(0, 3), (1, 0), (2, 0)],
              12, 12, 18, run_ladder=False),
    ]
    with open(ROOT / "data/a14/v2_redecomp_sweep.json", "w") as fh:
        json.dump(results, fh, indent=1)
    print("ALL HUNTS DONE.")


if __name__ == "__main__":
    main()

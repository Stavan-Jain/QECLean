"""A14 bb_108 presentation-orbit sweep: can any equivalent presentation
rescue a d = 20 double?

§14 refuted the stored presentation's safe floors (bb108-y by deficit 2,
bb108-x at the k-gate), but A11 proved literal-lift doubling is
presentation-sensitive: the cover depends on the *lift*, and equivalent
presentations re-route `im Δ` (hit3: stored x-cover d = 6, anchorable
presentation d = 12).  This sweeps the presentation orbit of
bb_108 [[108,8,10]] on Z9xZ6 under the cover-relevant equivalences:

- **doubled-axis translations** of A and B independently (undoubled-axis
  translations are exact cover symmetries: that coordinate has the same
  order upstairs and downstairs, so they cannot change the seams);
- **diagonal unit automorphisms** (x, y) -> (x^u, y^v), u in (Z/9)^x,
  v in (Z/6)^x (includes both inversions);
- **A <-> B swap**.

Mixing automorphisms (x -> x·y^b etc.) and the Z18xZ3 re-decomposition
of the same abstract group are documented NON-covered dimensions (v2).

Staged battery per cell: k-gate + S0 raw seams (fast probe, every cell)
-> S1+/S2 (S0 survivors) -> S4 orbit-rep SAT at floor 20 (cheap-tier
survivors) -> exact cover distance ladder (anything SF-certified).

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_bb108_orbit_sweep.py
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

L, M, D_BASE = 9, 6, 10
A0 = [(3, 0), (0, 1), (0, 2)]     # x^3 + y + y^2
B0 = [(0, 3), (1, 0), (2, 0)]     # y^3 + x + x^2
UNITS9 = [u for u in range(1, 9) if np.gcd(u, 9) == 1]
UNITS6 = [v for v in range(1, 6) if np.gcd(v, 6) == 1]


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


def enumerate_cells(axis: str):
    """Deduped (A, B) support pairs over the v1 equivalence set."""
    shifts = range(L) if axis == "x" else range(M)
    seen, cells = set(), []
    for u, v, swap in itertools.product(UNITS9, UNITS6, (False, True)):
        Au = {((u * e) % L, (v * f) % M) for (e, f) in A0}
        Bu = {((u * e) % L, (v * f) % M) for (e, f) in B0}
        if swap:
            Au, Bu = Bu, Au
        for ta, tb in itertools.product(shifts, shifts):
            if axis == "x":
                A2 = frozenset(((e + ta) % L, f) for (e, f) in Au)
                B2 = frozenset(((e + tb) % L, f) for (e, f) in Bu)
            else:
                A2 = frozenset((e, (f + ta) % M) for (e, f) in Au)
                B2 = frozenset((e, (f + tb) % M) for (e, f) in Bu)
            key = (A2, B2)
            if key not in seen:
                seen.add(key)
                cells.append((sorted(A2), sorted(B2)))
    return cells


def fast_probe(A, B, axis):
    """k-gate + S0 raw seam minimum (the free tier)."""
    Ac, Bc, lc, mc = canonical_row(A, B, L, M, axis)
    cov = XCover(Ac, Bc, lc, mc)
    kb, kc = h1_dim(cov.d2b, cov.d1b), h1_dim(cov.d2c, cov.d1c)
    if kb != kc:
        return {"gate": "k-fail", "k": kb, "k_cover": kc}
    ker = nullspace_f2(cov.d2b)
    kappa = ker.shape[0]
    s0 = None
    for bits in range(1, 1 << kappa):
        z = np.zeros(cov.nb, dtype=np.uint8)
        for i in range(kappa):
            if (bits >> i) & 1:
                z ^= ker[i]
        w = int(cov.seam(z).sum())
        s0 = w if s0 is None else min(s0, w)
    return {"gate": "ok", "k": kb, "s0_min": s0}


def main() -> None:
    t0 = time.time()
    all_rows = []
    survivors = []
    for axis in ("y", "x"):
        cells = enumerate_cells(axis)
        print(f"== axis {axis}: {len(cells)} unique presentation cells ==",
              flush=True)
        gate_fail, s0_hist = 0, Counter()
        for i, (A, B) in enumerate(cells):
            rec = {"axis": axis, "A": poly_str(A), "B": poly_str(B)}
            rec.update(fast_probe(A, B, axis))
            all_rows.append(rec)
            if rec["gate"] == "k-fail":
                gate_fail += 1
            else:
                s0_hist[rec["s0_min"]] += 1
                if rec["s0_min"] >= 2 * D_BASE:
                    survivors.append(rec)
                    print(f"  S0 SURVIVOR at cell {i}: axis {axis}, "
                          f"A = {rec['A']}, B = {rec['B']}, "
                          f"s0_min = {rec['s0_min']}", flush=True)
            if (i + 1) % 250 == 0:
                print(f"  ... {i + 1}/{len(cells)} "
                      f"({time.time() - t0:.0f}s)", flush=True)
        print(f"  axis {axis}: k-gate fails {gate_fail}/{len(cells)}; "
              f"S0 histogram {dict(sorted(s0_hist.items()))}", flush=True)

    print(f"\n== stage 2: S1+/S2 on {len(survivors)} S0 survivors ==",
          flush=True)
    finalists = []
    for rec in survivors:
        r2 = screen_row_phase2(
            [tuple(map(int, t)) for t in _parse(rec["A"])],
            [tuple(map(int, t)) for t in _parse(rec["B"])],
            L, M, rec["axis"], D_BASE)
        rec["cheap_min"] = r2["min_reached"]
        rec["cheap_reject"] = r2["reject"]
        print(f"  {rec['axis']}: {rec['A']} | {rec['B']} -> "
              f"descended min {r2['min_reached']} "
              f"({'REJECT' if r2['reject'] else 'PASS'})", flush=True)
        if not r2["reject"]:
            finalists.append(rec)

    print(f"\n== stage 3: S4 on {len(finalists)} finalists ==", flush=True)
    for rec in finalists:
        s4 = run_target(f"orbit-{rec['axis']}", rec["A"], rec["B"],
                        L, M, rec["axis"], D_BASE, conf_budget=10_000_000)
        rec["s4_status"] = s4["status"]
        if s4["status"] == "SF-CERTIFIED":
            print("  *** SF-CERTIFIED — running the cover distance ladder",
                  flush=True)
            from a14_d10_battery import cover_distance_ladder
            rec["cover"] = cover_distance_ladder(
                "bb108-orbit", rec["A"], rec["B"], L, M, rec["axis"],
                2 * D_BASE)

    with open(ROOT / "data/a14/bb108_orbit_sweep.json", "w") as fh:
        json.dump({"cells": all_rows, "survivors": survivors}, fh, indent=1)
    print(f"\nDONE ({time.time() - t0:.0f}s): {len(all_rows)} cells, "
          f"{len(survivors)} S0 survivors, {len(finalists)} finalists.")


def _parse(s: str):
    from a14_safe_floor_screens import parse_poly
    return parse_poly(s)


if __name__ == "__main__":
    main()

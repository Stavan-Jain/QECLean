"""A14 d=10-base battery: do bb_90 / bb_108 admit d=20 doubles?

The tower battery (§13) closed the same-axis re-doubling route: distance
freezes at d(rung-1). Larger distances must therefore come from
larger-d *bases*. The two d = 10 corpus codes are the first targets:

    bb_90  [[90,8,10]]  on Z15xZ3  (A = x^9+y+y^2, B = 1+x^2+x^7)
    bb_108 [[108,8,10]] on Z9xZ6   (A = x^3+y+y^2, B = y^3+x+x^2)

Both axes of each are *fresh* (trivial 2-part on the doubled axis — no
prior doubling), so the §13 toric bottleneck does not apply a priori.
A literal-lift double passing all four template conditions would be a
NEW [[180,8,20]] resp. [[216,8,20]] — the first doubling instance with
d > 12 in the program.

Per (code, axis): k-gate (condition 2, A12) -> cheap tiers (S0/S1+/S2)
-> S4 per G-orbit rep at floor 20 -> if SF-CERTIFIED, the payoff run:
the exact cover distance ladder (`x_distance`, lb=2 so every UNSAT step
is unconditional).

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_d10_battery.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from a14_phase2_screens import a14_columns  # noqa: E402
from a14_s4_ladder import run_target  # noqa: E402
from a14_safe_floor_screens import parse_poly  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

TARGETS = [
    ("bb90-x  [[90,8,10]]  -x-> [[180,8,20]]?",
     "x^9 + y + y^2", "1 + x^2 + x^7", 15, 3, "x", 10),
    ("bb90-y  [[90,8,10]]  -y-> [[180,8,20]]?",
     "x^9 + y + y^2", "1 + x^2 + x^7", 15, 3, "y", 10),
    ("bb108-x [[108,8,10]] -x-> [[216,8,20]]?",
     "x^3 + y + y^2", "y^3 + x + x^2", 9, 6, "x", 10),
    ("bb108-y [[108,8,10]] -y-> [[216,8,20]]?",
     "x^3 + y + y^2", "y^3 + x + x^2", 9, 6, "y", 10),
]


def cover_distance_ladder(name, As, Bs, l, m, axis, ub):
    """Exact cover d_X, every UNSAT step unconditional (lb = 2)."""
    from bb_lab.checks import bb_check_matrices
    from bb_lab.group import AbelianGroup
    from bb_lab.poly import Poly
    from bb_lab.sat_distance import x_distance
    dims = (2 * l, m) if axis == "x" else (l, 2 * m)
    G = AbelianGroup(dims)
    checks = bb_check_matrices(Poly.from_string(As, G), Poly.from_string(Bs, G))
    t0 = time.time()
    try:
        res = x_distance(checks, weight_lower_bound=2, weight_upper_bound=ub,
                         verbose=True)
        print(f"  {name}: cover d_X = {res.distance}  [{time.time()-t0:.0f}s]",
              flush=True)
        return {"d_X": int(res.distance)}
    except RuntimeError:
        print(f"  {name}: cover UNSAT through {ub} (d_X >= {ub + 1})  "
              f"[{time.time()-t0:.0f}s]", flush=True)
        return {"d_X_lower": ub + 1}


def main() -> None:
    t0 = time.time()
    results = []
    for name, As, Bs, l, m, axis, d in TARGETS:
        print(f"== {name} (floor {2 * d}) ==", flush=True)
        rec = {"name": name, "A": As, "B": Bs, "l": l, "m": m,
               "axis": axis, "d_base": d, "floor": 2 * d}
        cols = a14_columns(parse_poly(As), parse_poly(Bs), l, m, axis, d)
        rec.update(cols)
        if "a14_skip" in cols:
            rec["status"] = "K-GATE-FAIL (condition 2 dies)"
            print(f"  {rec['status']}", flush=True)
        elif cols["a14_screen_reject"]:
            rec["status"] = (f"SF-REFUTED (cheap tier: coset element of "
                             f"weight {cols['a14_cheap_min']} < {2 * d})")
            print(f"  raw seam min {cols['a14_s0_raw_min']}, cheap min "
                  f"{cols['a14_cheap_min']} -> {rec['status']}", flush=True)
        else:
            print(f"  cheap tiers pass (raw {cols['a14_s0_raw_min']}, "
                  f"descended {cols['a14_cheap_min']}); handing to S4",
                  flush=True)
            s4 = run_target(name, As, Bs, l, m, axis, d,
                            conf_budget=10_000_000)
            rec["s4"] = s4
            rec["status"] = s4["status"]
            if s4["status"] == "SF-CERTIFIED":
                print("  SF certified -> running the cover distance ladder",
                      flush=True)
                rec["cover"] = cover_distance_ladder(name, As, Bs, l, m,
                                                     axis, 2 * d)
        results.append(rec)
        print(f"  [{time.time() - t0:.0f}s elapsed]\n", flush=True)

    with open(ROOT / "data/a14/d10_battery.json", "w") as fh:
        json.dump(results, fh, indent=1)
    print("================= d=10-base battery summary =================")
    for r in results:
        line = f"  {r['name']}: {r['status']}"
        if "cover" in r:
            c = r["cover"]
            line += (f" | cover d_X = {c['d_X']}" if "d_X" in c
                     else f" | cover d_X >= {c['d_X_lower']}")
        print(line)
    print(f"({time.time() - t0:.0f}s)")


if __name__ == "__main__":
    main()

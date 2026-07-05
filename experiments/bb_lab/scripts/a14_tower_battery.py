"""A14 tower battery: rung-2 safe floors for every proven doubling instance.

Each proven rung-1 double (gross, pair72, hit3/4/6-y) is itself a BB code;
doubling the same axis again is the next rung of its Z_{2^r} tower (the
tour-de-gross shape).  A13 settled the k-row (deck-trivial towers keep k);
A12 makes condition 2 equivalent to the k-check; A14's battery decides
the remaining value-carrying input, the rung-2 safe floor:

    rung-2 SF  :=  SeamCosetFloor (2 * d(rung-1 cover))

Verdict semantics per target:
- k-gate fail  -> condition 2 dies at rung 2 (tower stops for a reason
  upstream of the floor);
- cheap-tier reject (S0/S1+/S2) -> SF-REFUTED with an explicit light
  coset element (certificate weight printed);
- else S4 per G-orbit representative (Prop A14.1(4) transport), CaDiCaL,
  conflict-budgeted: UNSAT on all reps -> SF-CERTIFIED (solver-grade);
  SAT -> SF-REFUTED (witness weight); budget-out -> INCONCLUSIVE.

Context for reading the numbers: the IBM tour-de-gross family grows
d = 6(2r + b - 1) — *linearly* — so its r = 2 member is [[288,12,18]],
not [[288,12,24]].  A rung-2 SF refutation with a light class in the
18–22 range would be a mechanism-level explanation of that linear
growth; a certification would be a new-code-grade surprise.

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_tower_battery.py
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

# (name, A, B, rung-1-cover group (l, m), axis doubled again, d(rung-1))
# The rung-1 cover is the rung-2 base; canonical same-exponent lifts mean
# the polynomial strings are unchanged along the tower.
TARGETS = [
    ("gross-rung2  [[144,12,12]] -x-> [[288,12,24]]?",
     "x^3 + y + y^2", "y^3 + x + x^2", 12, 6, "x", 12),
    ("pair72-rung2 [[72,4,8]]    -x-> [[144,4,16]]?",
     "x^2 + y + y^3", "1 + x + y^2", 6, 6, "x", 8),
    ("hit3y-rung2  [[144,12,12]] -y-> [[288,12,24]]?",
     "y^3 + x + x^2", "y + x*y^2 + x^2", 6, 12, "y", 12),
    ("hit4y-rung2  [[144,12,12]] -y-> [[288,12,24]]?",
     "y^3 + x + x^2", "y^2 + x*y^3 + x^2*y", 6, 12, "y", 12),
    ("hit6y-rung2  [[144,12,12]] -y-> [[288,12,24]]?",
     "y^3 + x + x^2", "x*y + x^2*y^2 + x^3", 6, 12, "y", 12),
]


def main() -> None:
    t0 = time.time()
    results = []
    for name, As, Bs, l, m, axis, d in TARGETS:
        print(f"== {name} (floor {2 * d}) ==")
        rec = {"name": name, "A": As, "B": Bs, "l": l, "m": m,
               "axis": axis, "d_base": d, "floor": 2 * d}
        cols = a14_columns(parse_poly(As), parse_poly(Bs), l, m, axis, d)
        rec.update(cols)
        if "a14_skip" in cols:
            rec["status"] = "K-GATE-FAIL (condition 2 dies at rung 2)"
            print(f"  {rec['status']}")
        elif cols["a14_screen_reject"]:
            rec["status"] = (f"SF-REFUTED (cheap tier: coset element of "
                             f"weight {cols['a14_cheap_min']} < {2 * d})")
            print(f"  raw seam min {cols['a14_s0_raw_min']}, cheap-tier min "
                  f"{cols['a14_cheap_min']} -> {rec['status']}")
        else:
            print(f"  cheap tiers pass (raw min {cols['a14_s0_raw_min']}, "
                  f"descended min {cols['a14_cheap_min']}); handing to S4")
            s4 = run_target(name, As, Bs, l, m, axis, d,
                            conf_budget=10_000_000)
            rec["s4"] = s4
            rec["status"] = s4["status"]
        results.append(rec)
        print(f"  [{time.time() - t0:.0f}s elapsed]\n")

    with open(ROOT / "data/a14/tower_battery.json", "w") as fh:
        json.dump(results, fh, indent=1)

    print("================= tower battery summary =================")
    for r in results:
        print(f"  {r['name']}: {r['status']}")
    print(f"({time.time() - t0:.0f}s)")


if __name__ == "__main__":
    main()

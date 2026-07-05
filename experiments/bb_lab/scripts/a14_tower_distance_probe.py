"""A14 tower follow-up: what IS the rung-2 distance once SF fails?

The tower battery refuted every rung-2 safe floor with light coset
elements of weight exactly d(rung-1) — half the doubling target.  A
light SAFE class does not by itself produce a light logical (the
overlap term can rescue, per the 41 A11 rescues), so the sharp question
is where d(rung-2 cover) actually lands in [d(rung-1), 2*d(rung-1)].

This probe walks the cover distance weight-by-weight with the lab's
exact per-weight SAT (`bb_lab.sat_distance.x_distance` with
`lb = ub = w`), so every step is an unconditional fact:

- pair72-rung2  [[144,4,?]]  on Z12xZ6 — full ladder from 2 to 16;
- gross-rung2   [[288,12,?]] on Z24xZ6 — from 12 up (witness-first;
  a SAT at 12 pins d <= 12 = d(rung-1): the tower freezes);
- hit3y-rung2   [[288,12,?]] on Z6xZ24 — same.

Reported values are d_X (the lab's convention for these families; the
overall d is <= d_X, so any d_X < 2d already kills the doubling value).

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_tower_distance_probe.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from bb_lab.checks import bb_check_matrices  # noqa: E402
from bb_lab.group import AbelianGroup  # noqa: E402
from bb_lab.poly import Poly  # noqa: E402
from bb_lab.sat_distance import x_distance  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

CASES = [
    ("pair72-rung2 [[144,4,?]] Z12xZ6", (12, 6),
     "x^2 + y + y^3", "1 + x + y^2", 2, 16),
    ("gross-rung2 [[288,12,?]] Z24xZ6", (24, 6),
     "x^3 + y + y^2", "y^3 + x + x^2", 12, 23),
    ("hit3y-rung2 [[288,12,?]] Z6xZ24", (6, 24),
     "y^3 + x + x^2", "y + x*y^2 + x^2", 12, 23),
]


def probe(name, dims, As, Bs, w_lo, w_hi):
    G = AbelianGroup(dims)
    checks = bb_check_matrices(Poly.from_string(As, G), Poly.from_string(Bs, G))
    rec = {"name": name, "dims": dims, "w_lo": w_lo, "w_hi": w_hi}
    t0 = time.time()
    try:
        res = x_distance(checks, weight_lower_bound=w_lo,
                         weight_upper_bound=w_hi, verbose=True)
        rec["d_X"] = int(res.distance)  # true witness weight (may be < w tried)
        print(f"  {name}: d_X = {res.distance}  "
              f"[{time.time() - t0:.0f}s]")
    except RuntimeError:  # ladder exhausted: UNSAT through w_hi
        rec["d_X_lower"] = w_hi + 1
        print(f"  {name}: UNSAT through {w_hi} (d_X >= {w_hi + 1})  "
              f"[{time.time() - t0:.0f}s]")
    return rec


def main() -> None:
    results = []
    for case in CASES:
        print(f"== {case[0]} ==", flush=True)
        try:
            results.append(probe(*case))
        except Exception as exc:
            results.append({"name": case[0], "error": repr(exc)})
            print(f"  ERROR: {exc!r}")
    with open(ROOT / "data/a14/tower_distance_probe.json", "w") as fh:
        json.dump(results, fh, indent=1)
    print("\n== summary ==")
    for r in results:
        print(f"  {r['name']}: "
              + (f"d_X = {r['d_X']}" if "d_X" in r else
                 f"d_X >= {r.get('d_X_lower', '?')}" if "d_X_lower" in r
                 else r.get("error", "?")))


if __name__ == "__main__":
    main()

"""A14 v2 endgame: S4 on the strongest bb_288 orbit cells.

The v2 sweep's Hunt B (bb_288 [[288,12,18]] presentation orbit, floor
36) produced cheap-tier passes at descended minima 36/40/48 before the
exhaustive stage was cut for cost.  We do not need every passing cell —
one SF-certified cell points at [[576,12,36]].  This runs the budgeted
per-orbit-rep S4 on a representative slate: three min-48 cells, two
min-40, one min-36 (all axis x; the log is the provenance:
`a14_v2_redecomp_sweep.py`, interrupted run).

Verdicts: UNSAT on all orbit reps -> SF-CERTIFIED (headline; the
[[576,12,36]] distance job is then a dedicated follow-up); any SAT ->
refuted with the witness weight; budget-out -> INCONCLUSIVE (honest).

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_bb288_s4_finalists.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from a14_s4_ladder import run_target  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

CELLS = [
    ("cell48-a", "1 + x^3*y^2 + x^3*y^7", "y^3 + x^2 + x^7"),
    ("cell48-b", "1 + x^3*y^2 + x^3*y^7", "x*y^3 + x^3 + x^8"),
    ("cell48-c", "x + x^4*y^2 + x^4*y^7", "y^3 + x^2 + x^7"),
    ("cell40-a", "y^2 + y^7 + x^3", "1 + x^2*y^3 + x^7"),
    ("cell40-b", "y^2 + y^7 + x^3", "x + x^3*y^3 + x^8"),
    ("cell36-a", "y^2 + y^7 + x^3", "y^3 + x^2 + x^7"),
]


def main() -> None:
    results = []
    for name, As, Bs in CELLS:
        print(f"== bb288 orbit {name}: A = {As}, B = {Bs} ==", flush=True)
        res = run_target(f"bb288-{name}", As, Bs, 12, 12, "x", 18,
                         conf_budget=20_000_000)
        results.append({"name": name, "A": As, "B": Bs, **res})
    with open(ROOT / "data/a14/bb288_s4_finalists.json", "w") as fh:
        json.dump(results, fh, indent=1)
    print("\n== summary ==")
    for r in results:
        print(f"  {r['name']}: {r['status']}")


if __name__ == "__main__":
    main()

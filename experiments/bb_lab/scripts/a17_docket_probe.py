"""A17: ladder-from-above probe of the INCONCLUSIVE docket.

For each above-floor docket cell (cheap_min > floor, S4 UNKNOWN at every
orbit rep), run budgeted witness-side SAT queries at weights BETWEEN the
floor and the cheap-tier minimum. Two probes per rep:

  w_hi = cheap_min - 2   ("is there anything the descent tiers missed?")
  w_mid = floor + (cheap_min - floor)//2  (midpoint softness)

A SAT answer maps the true coset minimum into a band (and, if it lands
below the floor, refutes SF outright — witness persisted). UNSAT at
w_hi is a *stronger-than-cheap-tier* lower bound on the class minimum.
UNKNOWN everywhere = the cell is genuinely solver-resistant both ways,
i.e. certification-flavored: queue for the dedicated high-budget /
XOR-aware pass.

Reads the docket straight from data/a17/corpus_battery*.jsonl.
Run from `experiments/bb_lab/`:
    uv run python scripts/a17_docket_probe.py [--conf-budget 300000]
"""

from __future__ import annotations

import argparse
import glob
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from a17_corpus_battery import coset_query_w  # noqa: E402
from a14_s4_ladder import orbit_reps  # noqa: E402
from a14_safe_floor_screens import XCover, canonical_row, parse_poly  # noqa: E402
from bb_lab.linalg import nullspace_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


def docket() -> list[dict]:
    seen: dict[tuple, dict] = {}
    for p in sorted(glob.glob(str(ROOT / "data/a17/corpus_battery*.jsonl"))):
        for line in open(p):
            r = json.loads(line)
            seen.setdefault((r["instance_id"], r["axis"]), r)
    return sorted(
        (r for r in seen.values()
         if r["status"] == "INCONCLUSIVE" and r["cheap_min"] > r["floor"]),
        key=lambda r: -(r["cheap_min"] - r["floor"]))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--conf-budget", type=int, default=300_000)
    args = ap.parse_args()

    rows = docket()
    print(f"{len(rows)} above-floor docket cells", flush=True)
    out = []
    t0 = time.time()
    for r in rows:
        A, B = parse_poly(r["A"]), parse_poly(r["B"])
        Ac, Bc, lc, mc = canonical_row(A, B, r["ell"], r["m"], r["axis"])
        cov = XCover(Ac, Bc, lc, mc)
        reps = orbit_reps(cov, nullspace_f2(cov.d2b))
        floor, cmin = r["floor"], r["cheap_min"]
        probes = sorted({cmin - 2, floor + (cmin - floor) // 2})
        rec = {"instance_id": r["instance_id"], "axis": r["axis"],
               "group": r["group"], "floor": floor, "cheap_min": cmin,
               "reps": []}
        print(f"== {r['instance_id']}:{r['axis']} [{r['group']}] "
              f"floor {floor}, cheap_min {cmin}, probes {probes} ==",
              flush=True)
        for i, z in enumerate(reps):
            seam = cov.seam(z)
            rrec = {"rep": i, "probes": {}}
            best = None
            for w in sorted(probes, reverse=True):
                if best is not None and best <= w:
                    continue  # already have a witness at/below this w
                v, wt, sup = coset_query_w(cov, seam, w, args.conf_budget)
                rrec["probes"][w] = {"verdict": v, "weight": wt}
                if v == "SAT":
                    rrec["probes"][w]["witness_support"] = sup
                    best = wt
                print(f"  rep {i} w<={w}: {v}"
                      + (f" (wt {wt})" if wt else "")
                      + f" [{time.time() - t0:.0f}s]", flush=True)
            rec["reps"].append(rrec)
        out.append(rec)
        with open(ROOT / "data/a17/docket_probe.json", "w") as fh:
            json.dump(out, fh, indent=1)
    print(f"done ({time.time() - t0:.0f}s)", flush=True)


if __name__ == "__main__":
    main()

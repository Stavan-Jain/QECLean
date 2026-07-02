"""A11 S4 — C-safe falsification check against A10's 13 unrescued bases.

A10 (Fork M) certified 13 bases whose ENTIRE 256-cover descent space
fails to double; by Lemma L1 the descent space is presentation-closed,
so in particular NO literal axis-lift of ANY equivalent presentation of
these codes doubles.  C-safe sufficiency therefore demands:

    for every presentation in the Aut × swap orbit and every axis,
    C-safe = [k preserved ∧ tight witness ∧ safe-floor ≥ 2d] is FALSE.

A single C-safe-true cell on any of the 13 refutes the criterion.  This
script sweeps all cells (tiny frames: Z₃×Z₃/Z₃×Z₄/Z₃×Z₅; full orbits)
and reports the conjunct-level failure breakdown.

Base list: `data/a10/s3_unrescued_bases.json` from the A10 branch
(pass --bases, or pipe `git show claude/a10-descent-twist-screen:...`
to a local file first).

Usage:
    git show claude/a10-descent-twist-screen:experiments/bb_lab/data/a10/s3_unrescued_bases.json > data/a11/s3_unrescued_bases.json
    uv run python scripts/a11_s4_thirteen.py [--bases data/a11/s3_unrescued_bases.json]
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.automorphism import automorphisms
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

from a9_lean_target_screen import profile_pair
from a11_s1_audit import poly_str

OUT = LAB_ROOT / "data" / "a11" / "s4_thirteen.jsonl"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", type=Path,
                    default=LAB_ROOT / "data" / "a11" / "s3_unrescued_bases.json")
    args = ap.parse_args()
    bases = json.loads(args.bases.read_text())
    print(f"{len(bases)} unrescued bases (A10 Fork-M certificates)")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    n_cells = n_csafe_true = 0
    t0 = time.time()
    with OUT.open("w") as fh:
        for rec in bases:
            ell, m = (int(t) for t in
                      rec["frame"].removeprefix("Z").split("xZ"))
            G = AbelianGroup((ell, m))
            A = Poly.from_string(rec["A"], G)
            B = Poly.from_string(rec["B"], G)
            seen: set[tuple[frozenset, frozenset]] = set()
            for phi in automorphisms(G):
                As, Bs = phi.apply_support(A.support), phi.apply_support(B.support)
                for Ps, Qs in ((As, Bs), (Bs, As)):
                    if (Ps, Qs) in seen:
                        continue
                    seen.add((Ps, Qs))
            breakdown = {"k_drop": 0, "no_wit": 0, "light_floor": 0, "CSAFE_TRUE": 0}
            for Ps, Qs in sorted(seen):
                for axis in ("x", "y"):
                    n_cells += 1
                    prow = {"instance_id": rec["instance_id"], "ell": ell, "m": m,
                            "A": poly_str(Ps), "B": poly_str(Qs),
                            "k": rec["k"], "d_base": rec["d_base"], "axis": axis}
                    prof = profile_pair(prow)
                    # k-preservation: rank-derived — profile computes the cover
                    # anyway; recompute k directly from its checks
                    from bb_lab.checks import bb_check_matrices
                    from bb_lab.codeparams import code_params
                    from a9_lean_target_screen import cover_group, lift_poly
                    Gc = cover_group(ell, m, axis)
                    kc = code_params(bb_check_matrices(
                        lift_poly(Poly(support=Ps, group=G), Gc),
                        lift_poly(Poly(support=Qs, group=G), Gc))).k
                    csafe = (kc == rec["k"] and prof["tight_witness"]
                             and prof["safe_floor_ok"])
                    if kc != rec["k"]:
                        breakdown["k_drop"] += 1
                    elif not prof["tight_witness"]:
                        breakdown["no_wit"] += 1
                    elif not prof["safe_floor_ok"]:
                        breakdown["light_floor"] += 1
                    if csafe:
                        breakdown["CSAFE_TRUE"] += 1
                        n_csafe_true += 1
                        print(f"  *** C-SAFE TRUE (criterion REFUTED?) "
                              f"{rec['instance_id']} {axis} A=`{poly_str(Ps)}` "
                              f"B=`{poly_str(Qs)}` ***", flush=True)
                    fh.write(json.dumps({**prow, "k_cover": kc,
                                         "tight_witness": prof["tight_witness"],
                                         "safe_floor_ok": prof["safe_floor_ok"],
                                         "safe_class_minima": prof["safe_class_minima"],
                                         "csafe": csafe}) + "\n")
            print(f"  {rec['instance_id']} ({rec['frame']}, d={rec['d_base']}): "
                  f"{2*len(seen)} cells -> {breakdown}", flush=True)
    print(f"\nTOTAL: {n_cells} cells, C-safe true on {n_csafe_true} "
          f"({'REFUTED' if n_csafe_true else 'consistent — 13/13 codes C-safe-false everywhere'}) "
          f"({time.time()-t0:.0f}s) -> {OUT}")


if __name__ == "__main__":
    main()

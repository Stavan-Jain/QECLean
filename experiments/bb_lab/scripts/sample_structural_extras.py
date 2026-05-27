"""Tier-1 v2 — add small samples in three structural niches the round-1
corpus is blind to.

Targets (a few-instances-each is enough; goal is structural coverage,
not quantity):

  1. Z_6 × Z_15  — non-semisimple multi-prime mixed-rank.
     G = Z_2 × Z_3² × Z_5, |G|=90, n=180. bb_90's G_odd structure
     plus a Z_2 factor (no Bravyi instance combines both).

  2. Z_3 × Z_35  — triple-prime G_odd (semisimple).
     G = Z_3 × Z_5 × Z_7, |G|=105, n=210. Three odd primes; the
     existing corpus has at most two.

  3. Z_8 × Z_9   — larger G_2 (cyclic Z_8).
     G = Z_8 × Z_3², |G|=72, n=144. Same |G| as gross but with
     G_2 = Z_8 (Z_2-rank 1) vs gross's G_2 = Z_4×Z_2 (Z_2-rank 2).

Reuses the `_bb90_perturbations` generator from sample_gross_neighborhood
(it's parameterized over (ell, m); the bb_90-shape templates produce
weight-3 polynomial pairs in any group).

Run after sample_gross_neighborhood.py has populated the corpus baseline.
"""

from __future__ import annotations

import time

# Importing from the sibling script — they live in the same dir.
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sample_gross_neighborhood import _bb90_perturbations, _sample_group


def main() -> None:
    t0 = time.time()
    print("Tier-1 v2 structural extras")
    total = 0
    # Niche 1: non-semisimple multi-prime mixed-rank.
    total += _sample_group(6, 15, _bb90_perturbations, "bb_neigh_z6z15")
    total += _sample_group(15, 6, _bb90_perturbations, "bb_neigh_z15z6")
    # Niche 2: triple-prime G_odd.
    total += _sample_group(3, 35, _bb90_perturbations, "bb_neigh_z3z35")
    total += _sample_group(5, 21, _bb90_perturbations, "bb_neigh_z5z21")
    # Niche 3: bigger G_2.
    total += _sample_group(8, 9, _bb90_perturbations, "bb_neigh_z8z9")
    dt = time.time() - t0
    print(f"done: {total} new canonical instances in {dt:.1f}s")


if __name__ == "__main__":
    main()

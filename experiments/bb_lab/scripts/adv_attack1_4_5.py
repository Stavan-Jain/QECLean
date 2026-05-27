"""Adversarial Attack 1: test R1+R4 conjecture on case (4, 5) over Z_12 × Z_12.

The H_UNIT² investigation flagged this instance as a falsifier of the
H_UNIT² tight refinement. Its R4 (cross-orbit) bound was never explicitly
computed against d. This script does that test.

Case: A = x^3 + y^4 + y^5, B = y^3 + x + x^2  over  Z_12 × Z_12.
Hypothesis: |A|=|B|=3 odd, G_odd = Z_3 × Z_3 elem-ab, c = 3.
Empirical d_X = 12 (per H_UNIT² note, from SAT).

Conjecture: d_X >= ceil(min(R4_A, R4_B) / c).

Outcomes:
  - If R4 bound <= 12: conjecture survives on this instance.
  - If R4 bound  > 12: conjecture FALSIFIED.
"""

from __future__ import annotations

import sys
import time

# Make the parent script's imports work
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))

from tier3_cv3_r4_crossorbit import test_case
from bb_lab.group import ZmZn


def main():
    print("=== Adversarial Attack 1: case (4, 5) on Z_12 × Z_12 ===\n", flush=True)

    # The H_UNIT² falsifier
    G = ZmZn(12, 12)
    A_str = "x^3 + y^4 + y^5"
    B_str = "y^3 + x + x^2"

    print(f"  G        = {G.label()}  (|G| = {G.cardinality})")
    print(f"  A        = {A_str}")
    print(f"  B        = {B_str}")
    print(f"  Expected: d_X = 12 (per H_UNIT² note, from SAT)\n")
    print("  Running test_case (SAT may take ~minutes for n=288)...\n", flush=True)

    t0 = time.time()
    r = test_case(
        label="(4,5) on Z_12×Z_12 — H_UNIT² falsifier of per-orbit",
        G=G, A_str=A_str, B_str=B_str,
        max_d=13,           # bound R4 may overshoot; test up to 13
        skip_sat=False,
    )
    elapsed = time.time() - t0

    print(f"  --- RESULTS ---")
    print(f"  n = {r.n}, k = {r.k}, c = {r.c}, elem_ab = {r.elem_ab}")
    print(f"  d_X (from SAT) = {r.d}")
    print(f"  C-v3 per-orbit bound = {r.bound_orig}")
    print(f"  R4 cross-orbit bound = {r.bound_r4}")
    print(f"  R4 info: {r.info}")
    print(f"  Total elapsed: {elapsed:.1f}s\n")

    # Verdict
    d_used = r.d if r.d is not None else 12   # fall back to published if SAT failed
    print(f"  --- VERDICT ---")
    print(f"  Hypothesis domain: ", end="")
    in_domain = (r.elem_ab and r.c >= 3)
    print("YES" if in_domain else "NO")
    if not in_domain:
        print(f"    (elem_ab={r.elem_ab}, c={r.c})")
        return
    print(f"  weight(A) = {len(A_str.split('+'))} (odd ✓)")
    print(f"  weight(B) = {len(B_str.split('+'))} (odd ✓)")

    if r.bound_r4 is None:
        print(f"  R4 evaluator returned None (basis dim too large)")
        return
    if r.bound_r4 > d_used:
        print(f"\n  *** CONJECTURE FALSIFIED ***")
        print(f"    R4 bound = {r.bound_r4} > d_X = {d_used}")
        print(f"    Gap = +{r.bound_r4 - d_used}")
    elif r.bound_r4 == d_used:
        print(f"\n  tight: R4 bound = d_X = {d_used}")
    else:
        print(f"\n  loose-correct: R4 bound = {r.bound_r4} < d_X = {d_used} (gap {d_used - r.bound_r4})")


if __name__ == "__main__":
    main()

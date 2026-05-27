"""Adversarial Attack 3: BB codes on G_odd = Z_3 × Z_7 (multi-prime).

The conjecture's empirical evidence is dominated by G_odd = Z_3 × Z_3
(roughly all Bravyi codes, most of the 74-row in-scope corpus). The
multi-prime G_odd case has been tested in only 1 testable instance
(B5: Z_7 × Z_7 with x+x³, y+y³).

This attack uses G = Z_6 × Z_7 (= Z_2 × Z_3 × Z_7), so:
  G_odd = Z_3 × Z_7  (loose elem-ab: rank 1 for each prime ✓)
  G_2 = Z_2

We pick A and B by hand to get c = 3 and k > 0:
  A = 1 + x + x^2          # supp = {(0,0), (1,0), (2,0)} ⊂ Z_6 × {0}, generates Z_6 × {0}
  B = 1 + y + x^3          # supp = {(0,0), (0,1), (3,0)} ⊂ {0,3} × Z_7
                           # generates ⟨(0,1), (3,0)⟩ = {0,3} × Z_7, |G_b| = 14
  G_a ∩ G_b = {0,3} × {0}, order 2
  c = |G_a| / |G_a ∩ G_b| = 6/2 = 3  ✓

We also probe several variant polynomial choices to widen coverage.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from tier3_cv3_r4_crossorbit import test_case
from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.degeneracy import is_g_odd_elementary_abelian
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import joint_support_subgroup_index


CASES = [
    # (label, ell, m, A_str, B_str, max_d)
    # For multi-prime G_odd we need BOTH A and B to vanish on at least one orbit
    # — picking A with Z_p1-vanishing and B with Z_p2-vanishing won't intersect.
    # The trick: both A and B must contain the SAME prime's cube/p-root sum.

    # Z_6 × Z_5  (G_odd = Z_3 × Z_5, G_2 = Z_2)
    # A cube-vanish via Z_3-sum on x-axis, B fifth-vanish via Z_5-sum on y-axis
    ("Z6xZ5  cube-x / 5th-y (both fully-axis-vanishing)",
        6, 5, "1 + x + x^2", "1 + y + y^2 + y^3 + y^4", 10),
    # Variants with shifts
    ("Z6xZ5  cube-x shifted / 5th-y",
        6, 5, "1 + x^2 + x^4", "1 + y + y^2 + y^3 + y^4", 10),
    ("Z6xZ5  cube-x / shifted-5th-y",
        6, 5, "1 + x + x^2", "y + y^2 + y^3 + y^4 + 1", 10),
    # Different weights — try mixing
    ("Z6xZ5  weight-3/3 cube/cube on x (B = A·y) — degenerate test",
        6, 5, "1 + x + x^2", "y + x*y + x^2*y", 10),
    # Z_6 × Z_5 with B containing cube-root vanishing on x-axis (so both A, B have Z_3 vanishing)
    ("Z6xZ5  both-cube-x",
        6, 5, "1 + x + x^2", "1 + x^2 + x^4 + y + x*y", 10),
    # Z_10 × Z_3 = Z_2 × Z_5 × Z_3 (G_odd = Z_3 × Z_5; G_2 = Z_2)
    ("Z10xZ3 5th-y / cube-x",
        10, 3, "1 + y + y^2", "1 + x + x^2 + x^3 + x^4", 10),
    # Z_3 × Z_15 = Z_3 × Z_3 × Z_5 = (Z_3)² × Z_5 (multi-prime, BOTH primes elem-ab)
    # G_2 trivial, semisimple!
    ("Z3xZ15 (semisimple multi-prime) cube/5th",
        3, 15, "1 + x + x^2", "1 + y + y^2 + y^3 + y^4", 10),
    # Z_6 × Z_15: G_odd = Z_3 × Z_3 × Z_5 (loose elem-ab), G_2 = Z_2
    ("Z6xZ15 nonsemisimple multi-prime",
        6, 15, "1 + x + x^2", "1 + y + y^2 + y^3 + y^4", 10),
]


def main():
    print("=== Adversarial Attack 3: G_odd = Z_3 × Z_7 (multi-prime) ===\n", flush=True)

    n_inscope = 0
    n_tested = 0
    n_violations = 0
    n_tight = 0
    n_loose = 0
    n_kzero = 0
    n_outscope = 0
    violators: list[dict] = []

    for label, ell, m, A_str, B_str, max_d in CASES:
        G = ZmZn(ell, m)
        try:
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
        except Exception as exc:
            print(f"  [{label}] PARSE FAIL: {exc}", flush=True)
            continue
        c = joint_support_subgroup_index(A, B, G)
        elem_ab = is_g_odd_elementary_abelian(G)
        in_hypothesis = (c >= 3) and elem_ab

        # Get n, k cheaply first
        try:
            checks = bb_check_matrices(A, B)
            params = code_params(checks)
            n, k = params.n, params.k
        except Exception as exc:
            print(f"  [{label}] CHECKS FAIL: {exc}", flush=True)
            continue

        print(f"  [{label}]")
        print(f"    G = {G.label()}  A = {A_str}  B = {B_str}")
        print(f"    n = {n}, k = {k}, c = {c}, elem_ab = {elem_ab}, in_hypothesis = {in_hypothesis}")

        if not in_hypothesis:
            n_outscope += 1
            print(f"    OUT OF HYPOTHESIS DOMAIN — skipped\n", flush=True)
            continue
        if k == 0:
            n_kzero += 1
            print(f"    k = 0 (no logicals) — skipped\n", flush=True)
            continue

        n_inscope += 1

        # Run test_case to compute SAT and R4
        t0 = time.time()
        r = test_case(label=label, G=G, A_str=A_str, B_str=B_str,
                      max_d=max_d, skip_sat=False)
        elapsed = time.time() - t0
        print(f"    R4 info: {r.info}")
        print(f"    bound_orig (per-orbit) = {r.bound_orig}")
        print(f"    bound_r4   (cross-orbit) = {r.bound_r4}")
        print(f"    d_X = {r.d}")
        print(f"    elapsed: {elapsed:.1f}s")

        if r.bound_r4 is None:
            print(f"    R4 UNABLE (basis dim too large)\n", flush=True)
            continue
        if r.d is None:
            print(f"    SAT could not determine d\n", flush=True)
            continue

        n_tested += 1
        if r.bound_r4 > r.d:
            n_violations += 1
            violators.append({"label": label, "A": A_str, "B": B_str,
                              "G": G.label(), "c": c, "k": k,
                              "bound_r4": r.bound_r4, "d": r.d})
            print(f"    *** CONJECTURE FALSIFIED *** R4 = {r.bound_r4} > d = {r.d}\n", flush=True)
        elif r.bound_r4 == r.d:
            n_tight += 1
            print(f"    tight: R4 = d = {r.d}\n", flush=True)
        else:
            n_loose += 1
            print(f"    loose-correct: R4 = {r.bound_r4} < d = {r.d} (gap {r.d - r.bound_r4})\n", flush=True)

    print(f"\n=== Summary ===")
    print(f"  Total cases:         {len(CASES)}")
    print(f"  Out of hypothesis:   {n_outscope}")
    print(f"  k = 0 (no logicals): {n_kzero}")
    print(f"  In-scope tested:     {n_tested}")
    print(f"  Tight:               {n_tight}")
    print(f"  Loose-correct:       {n_loose}")
    print(f"  **Violations:**      {n_violations}")
    if n_violations > 0:
        print(f"\n  *** CONJECTURE FALSIFIED on G_odd = Z_3 × Z_7 ***")
        for v in violators:
            print(f"    {v}")
    elif n_tested == 0:
        print(f"\n  Inconclusive: no in-scope k>0 instance succeeded.")
        print(f"  This is itself a flag: the multi-prime regime may not")
        print(f"  produce k>0 codes for c≥3 polynomials we can construct by hand.")
    else:
        print(f"\n  Conjecture SURVIVES this attack on G_odd = Z_3 × Z_7 ({n_tested} tested).")


if __name__ == "__main__":
    main()

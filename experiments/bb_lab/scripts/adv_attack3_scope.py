"""Probe the structural scope of the Z_3 × Z_15 falsifier.

Found: A = 1+x+x², B = 1+y+y²+y³+y⁴ on Z_3 × Z_15 has R4=4 > d_X=2.

Open questions about the failure mode:
  Q1. Is the falsifier specific to SEMISIMPLE G (|G| odd, G_2 trivial)?
      Test the same A, B on a non-semisimple variant.
  Q2. Does single-prime G_odd save it? Restrict to G_odd = (Z_p)^k single prime.
      The current falsifier has G_odd = Z_3² × Z_5 (multi-prime).
  Q3. Lin-Pryadko's d_A^⊥ is satisfied; is it ALWAYS satisfied while R4 fails?
      That is, can we engineer an instance where Lin-Pryadko itself fails?
      (If yes, something is wrong in the setup — we'd be falsifying a proven
      theorem.)
"""

from __future__ import annotations

import sys
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
    # The original falsifier (semisimple G, multi-prime G_odd)
    ("REFERENCE: Z_3xZ_15 (semisimple, multi-prime) — KNOWN FALSIFIER",
        3, 15, "1 + x + x^2", "1 + y + y^2 + y^3 + y^4", 10),
    # Variants with G_2 non-trivial (Z_3 × Z_15 → Z_6 × Z_15, etc.)
    ("Z_6xZ_15: c?-version with A on Z_3-subgroup",
        6, 15, "1 + x^2 + x^4", "1 + y + y^2 + y^3 + y^4", 10),
    ("Z_3xZ_30: G_2=Z_2 on second factor only",
        3, 30, "1 + x + x^2", "1 + y^2 + y^4 + y^6 + y^8", 10),
    # Non-semisimple, but single-prime G_odd? — need G with G_odd a single (Z_p)^k.
    # No 5 → just (Z_3)^k.  E.g. Z_6 × Z_6 (already in corpus, well-tested).
    # The simplest test: Z_3 × Z_3 (semisimple, single-prime). Does the analog falsify?
    # Need a polynomial on Z_3 with cube-root vanishing (A=1+x+x²) and one on Z_3 with
    # cube-root vanishing in DIFFERENT direction (B=1+y+y²). What does R4 give?
    ("Z_3xZ_3 (semisimple, single-prime) analog",
        3, 3, "1 + x + x^2", "1 + y + y^2", 6),
    # And Z_3 × Z_9 (semisimple, NON-elem-ab Z_9 part) — out of hypothesis
    ("Z_3xZ_9 (semisimple, NON-elem-ab) — should be excluded",
        3, 9, "1 + x + x^2", "1 + y + y^2 + y^3 + y^4 + y^5 + y^6 + y^7 + y^8", 8),
    # Z_15 × Z_15 = Z_3 × Z_5 × Z_3 × Z_5 (semisimple, two-prime, rank-2 each)
    ("Z_15xZ_15 (semisimple, multi-prime, higher rank)",
        15, 15, "1 + x + x^2", "1 + y + y^2 + y^3 + y^4", 10),
    # Test whether the Lin-Pryadko base bound (d_A^⊥/c) also exceeds d on the falsifier.
    # If yes, we'd be falsifying a proven theorem — alarm bell. If no, R4 is the issue.
    # (This is checked by `adv_attack3_verify.py` for the original falsifier.)
]


def main():
    print("=== Adversarial Attack 3 SCOPE PROBE ===\n", flush=True)
    print("  Question: does the Z_3 × Z_15 falsifier generalize, and to what?\n", flush=True)
    print(f"{'Label':<60} {'c':>3} {'k':>4} {'orig':>5} {'R4':>5} {'d':>4} {'verdict':<15}")
    print("-" * 110, flush=True)

    falsifiers = []
    for label, ell, m, A_str, B_str, max_d in CASES:
        G = ZmZn(ell, m)
        try:
            A = Poly.from_string(A_str, G)
            B = Poly.from_string(B_str, G)
        except Exception as exc:
            print(f"  [{label}] PARSE FAIL: {exc}", flush=True)
            continue

        elem_ab = is_g_odd_elementary_abelian(G)
        c = joint_support_subgroup_index(A, B, G)
        checks = bb_check_matrices(A, B)
        params = code_params(checks)
        if params.k == 0:
            print(f"  {label:<60} {c:>3} {params.k:>4} {'-':>5} {'-':>5} {'-':>4} {'k=0':<15}")
            continue
        if c < 3 or not elem_ab:
            print(f"  {label:<60} {c:>3} {params.k:>4} {'-':>5} {'-':>5} {'-':>4} {'out':<15}")
            continue

        r = test_case(label, G, A_str, B_str, max_d=max_d, skip_sat=False)
        if r.bound_r4 is None:
            verdict = "R4 UNABLE"
        elif r.d is None:
            verdict = "SAT fail"
        elif r.bound_r4 > r.d:
            verdict = f"*VIOLATES* gap +{r.bound_r4 - r.d}"
            falsifiers.append((label, A_str, B_str, G.label(), c, r.bound_r4, r.d))
        elif r.bound_r4 == r.d:
            verdict = "tight"
        else:
            verdict = f"loose gap -{r.d - r.bound_r4}"
        print(f"  {label:<60} {c:>3} {r.k:>4} {str(r.bound_orig):>5} {str(r.bound_r4):>5} "
              f"{str(r.d):>4} {verdict:<15}", flush=True)

    print("\n=== Summary ===")
    if falsifiers:
        print(f"  Falsifiers found ({len(falsifiers)}):")
        for f in falsifiers:
            print(f"    {f[3]:<10} A={f[1]!r:<22} B={f[2]!r:<28} c={f[4]} R4={f[5]} d={f[6]}")
    else:
        print(f"  No falsifiers in this probe set.")


if __name__ == "__main__":
    main()

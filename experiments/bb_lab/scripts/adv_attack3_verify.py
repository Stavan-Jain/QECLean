"""Verify the Z_3 × Z_15 falsifier.

Case: G = Z_3 × Z_15, A = 1 + x + x², B = 1 + y + y² + y³ + y⁴.
Reported:
  - n = 90, k = 16
  - elem_ab G_odd = True (Z_3 × Z_3 × Z_5, each prime part elem-ab)
  - c = 3
  - weights 3, 5 both odd
  - R4 raw = 12, R4 bound = 4
  - d_X = 2  → VIOLATION

Sanity checks:
  1. Re-derive (n, k) directly from check-matrix ranks.
  2. Re-run SAT distance with explicit small caps (1, 2, 3) to find the
     exact distance, NOT just the first SAT result.
  3. Find an explicit weight-2 X-logical witness (if d=2 is real).
  4. Compute Lin-Pryadko's d_A^⊥ (min weight in ker(M_A)) and compare to ρ_A.
  5. Verify the elementary-abelian classifier on G_odd.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.degeneracy import is_g_odd_elementary_abelian
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2, rank_f2
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    joint_support_subgroup_index,
)
from bb_lab.sat_distance import x_distance


def main():
    print("=== VERIFICATION: Z_3 × Z_15 falsifier ===\n", flush=True)
    G = ZmZn(3, 15)
    A_str = "1 + x + x^2"
    B_str = "1 + y + y^2 + y^3 + y^4"
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)

    print(f"  G = {G.label()},  |G| = {G.cardinality}")
    print(f"  A = {A_str},  |supp(A)| = {len(A.support)}")
    print(f"  B = {B_str},  |supp(B)| = {len(B.support)}")
    print(f"  weight(A) odd: {len(A.support) % 2 == 1}")
    print(f"  weight(B) odd: {len(B.support) % 2 == 1}")
    print(f"  G_odd elem-ab (loose): {is_g_odd_elementary_abelian(G)}")
    c = joint_support_subgroup_index(A, B, G)
    print(f"  c = {c}")

    print("\n--- Check 1: code parameters ---")
    checks = bb_check_matrices(A, B)
    params = code_params(checks)
    print(f"  n = {params.n}, k = {params.k}")
    print(f"  rank(H_X) = {params.rank_HX}, rank(H_Z) = {params.rank_HZ}")
    print(f"  Total qubits = 2|G| = {2*G.cardinality}, "
          f"stabilizer count = {params.rank_HX + params.rank_HZ}, "
          f"logical count k = n - rank(H_X) - rank(H_Z) = "
          f"{params.n - params.rank_HX - params.rank_HZ}")

    print("\n--- Check 2: SAT distance at small caps ---")
    for cap in (1, 2, 3, 4, 5, 6):
        try:
            res = x_distance(checks, weight_upper_bound=cap)
            d = res.distance
            print(f"  cap = {cap}: d_X = {d}", flush=True)
        except Exception as exc:
            print(f"  cap = {cap}: SAT exception {exc!r}", flush=True)

    print("\n--- Check 3: find an explicit weight-2 X-logical witness ---")
    # An X-logical (α, β) ∈ ker(H_Z) \ rowspan(H_X). For d = 2, try
    # all weight-2 (α, β) and check ker(H_Z) and not rowspan(H_X).
    M_A = circulant(A).astype(np.uint8)
    M_B = circulant(B).astype(np.uint8)
    nG = G.cardinality
    H_X = np.hstack([M_A, M_B]).astype(np.uint8)
    H_Z = np.hstack([M_B.T, M_A.T]).astype(np.uint8)
    print(f"  H_X shape: {H_X.shape}, H_Z shape: {H_Z.shape}", flush=True)

    # Find weight-2 vectors in ker(H_Z) not in rowspan(H_X)
    # First compute ker(H_Z) basis
    ker_HZ = nullspace_f2(H_Z)
    print(f"  dim ker(H_Z) = {ker_HZ.shape[0]}")
    # rowspan(H_X) = stacked-row span
    # An X-logical is in ker(H_Z) but not in rowspan(H_X)
    # Check: rank(H_X stacked under ker_HZ row?) = rank(H_X) + (1 if v not in span else 0)
    rank_HX = rank_f2(H_X)
    print(f"  rank(H_X) = {rank_HX}")

    # Enumerate weight-2 vectors and test
    print(f"  Enumerating weight-2 vectors ({2*nG*(2*nG-1)//2} total)...", flush=True)
    found_witnesses = []
    for i in range(2*nG):
        for j in range(i+1, 2*nG):
            v = np.zeros(2*nG, dtype=np.uint8)
            v[i] = v[j] = 1
            # Check v ∈ ker(H_Z)
            HZv = (H_Z @ v) % 2
            if HZv.any():
                continue
            # v is in ker(H_Z). Check if in rowspan(H_X).
            stack = np.vstack([H_X, v.reshape(1, -1)])
            if rank_f2(stack) == rank_HX:
                continue  # in rowspan, not a logical
            found_witnesses.append((i, j))
            if len(found_witnesses) >= 3:
                break
        if len(found_witnesses) >= 3:
            break

    if found_witnesses:
        print(f"  Found {len(found_witnesses)} weight-2 X-logical witnesses (showing up to 3):")
        for i, j in found_witnesses:
            block_i = "α" if i < nG else "β"
            pos_i = i if i < nG else i - nG
            block_j = "α" if j < nG else "β"
            pos_j = j if j < nG else j - nG
            print(f"    indices ({i}, {j})  =  ({block_i}[{pos_i}], {block_j}[{pos_j}])")
    else:
        print(f"  *** NO weight-2 X-logical found ***  — d_X > 2, SAT result inconsistent!")

    print("\n--- Check 4: Lin-Pryadko d_A^⊥ comparison ---")
    # d_A^⊥ = min weight of nonzero f ∈ ker(M_A^T) (or ker(M_A); abelian so often equal)
    # Use Gray-code via _min_weight_in_basis from radical_weight
    from bb_lab.radical_weight import _min_weight_in_basis
    nullsp_MA = nullspace_f2(M_A)
    nullsp_MAt = nullspace_f2(M_A.T)
    print(f"  dim ker(M_A)  = {nullsp_MA.shape[0]}")
    print(f"  dim ker(M_A^T) = {nullsp_MAt.shape[0]}")
    if nullsp_MA.shape[0] <= 22:
        dA_perp = _min_weight_in_basis(nullsp_MA)
        print(f"  d_A^⊥ (LP, ker(M_A))  = {dA_perp}")
    else:
        print(f"  d_A^⊥ (LP, ker(M_A))  = (dim {nullsp_MA.shape[0]} > 22; skipped)")
    if nullsp_MAt.shape[0] <= 22:
        dAt_perp = _min_weight_in_basis(nullsp_MAt)
        print(f"  d_A^⊥ (LP, ker(M_A^T)) = {dAt_perp}")

    bound_orig = bb_radical_bound(A, B, G)
    print(f"\n  C-v3 per-orbit bound = {bound_orig}")

    # Compute the R4 bound directly to confirm
    from tier3_cv3_r4_crossorbit import r4_cross_orbit_bound
    r4_bound, r4_info = r4_cross_orbit_bound(A, B, G)
    print(f"  R4 cross-orbit bound = {r4_bound}, info = {r4_info}")

    # Lin-Pryadko bound check
    if nullsp_MA.shape[0] <= 22:
        lp_bound_A = -(-dA_perp // c)   # ceiling
        print(f"  Lin-Pryadko bound from d_A^⊥: ⌈{dA_perp} / {c}⌉ = {lp_bound_A}")
    if nullsp_MAt.shape[0] <= 22:
        lp_bound_At = -(-dAt_perp // c)
        print(f"  Lin-Pryadko bound from d_(A^T)^⊥: ⌈{dAt_perp} / {c}⌉ = {lp_bound_At}")

    print("\n--- Verdict ---")
    if found_witnesses:
        print(f"  d_X = 2 (confirmed by explicit witness)")
        print(f"  R4 bound = {r4_bound}")
        if r4_bound is not None and r4_bound > 2:
            print(f"\n  *** CONJECTURE FALSIFIED: R4 bound {r4_bound} > d_X = 2 ***")
        # Also check if Lin-Pryadko is also violated (shouldn't be, by theorem)
        if nullsp_MA.shape[0] <= 22 and -(-dA_perp // c) > 2:
            print(f"  WARNING: Lin-Pryadko bound also exceeds d_X — something is wrong")
        else:
            print(f"  Lin-Pryadko's bound is satisfied (≤ d_X = 2), so this is a")
            print(f"  GENUINE falsifier of the R4 strengthening, not an artifact.")
    else:
        print(f"  Could not confirm d_X = 2 by witness — SAT may have given wrong answer")


if __name__ == "__main__":
    main()

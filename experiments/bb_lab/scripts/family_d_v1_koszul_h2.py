"""Family D v1 — Koszul H_2 cheap probe (round-2 v2 first session).

The Koszul complex of the regular(ish) sequence (A, B) over F_2[G]:

    0 → F_2[G] -d_2→ F_2[G]^2 -d_1→ F_2[G] → F_2[G]/(A,B) → 0
                γ ↦ (Bγ, Aγ)     (α, β) ↦ Aα + Bβ

For BB(G, A, B), under the standard correspondence
  - dim H_0(K) = k (Bravyi-Cross identity for the BB family)
  - H_1(K) = X-logical space (Koszul reformulation of d_X)
  - H_2(K) = ker(d_2) = Ann(A) ∩ Ann(B)  (the joint annihilator)

By the symmetry of (A, B) under the F_2[G]-self-duality of the BB code,
dim H_2 = dim H_0 = k / 2 (or similar; for Bravyi codes this is non-zero).

HYPOTHESIS (4d): There exists a function φ such that

       d_X ≥ φ( min weight in H_2(K) \\ {0} )

with φ monotone non-decreasing. If φ is even just φ(t) = t (a direct
weight-in-H_2 ≥ ?-style bound), this would give a Family D bound.

This script:
  1. Builds the Koszul complex for each Bravyi instance.
  2. Computes a basis for H_2 = ker(M_A) ∩ ker(M_B) over F_2.
  3. Brute-force computes the minimum non-zero weight in H_2.
  4. Compares against the known d_X.

If min |H_2| correlates with d_X (or, weaker, gives any non-trivial
lower bound), this is a viable Family D candidate. If not, we document
the negative result with a precise mechanism.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from pathlib import Path

import numpy as np
import yaml

from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2, rank_f2
from bb_lab.poly import Poly


@dataclass(frozen=True)
class KoszulProbeResult:
    code_id: str
    ell: int
    m: int
    G_order: int
    A_weight: int
    B_weight: int
    d_X_true: int
    rank_M_A: int
    rank_M_B: int
    dim_H_2: int          # F_2-dimension of Ann(A) ∩ Ann(B)
    min_weight_H_2: int   # minimum Hamming weight of a nonzero vector
    dim_ann_A: int        # dim ker M_A
    dim_ann_B: int        # dim ker M_B

    def gap(self) -> int:
        """How much we'd be loose by: d_X_true - min_weight_H_2."""
        return self.d_X_true - self.min_weight_H_2

    def ratio(self) -> float:
        return self.min_weight_H_2 / self.d_X_true if self.d_X_true else float("nan")


def koszul_h2_basis(M_A: np.ndarray, M_B: np.ndarray) -> np.ndarray:
    """Return a basis (rows) for the F_2-subspace Ann(A) ∩ Ann(B).

    Equivalently: ker([M_A ; M_B])  where ; is vertical stacking.
    Shape: (dim_H_2, |G|).
    """
    # Both M_A and M_B are |G| × |G|; stacking gives 2|G| × |G|.
    stacked = np.concatenate([M_A, M_B], axis=0)
    return nullspace_f2(stacked)


def min_weight_in_subspace(basis: np.ndarray, cap: int | None = None) -> int:
    """Minimum Hamming weight of a nonzero F_2-linear combination of basis rows.

    Brute-force enumerates all 2^k - 1 nonzero combinations for k =
    basis.shape[0]. Fast for k ≤ 16. For larger k, we cap via successive
    subsets up to a threshold and document the bound.

    Returns the minimum weight found; if `cap` is set, returns the min
    over subsets of size ≤ cap (an UPPER bound on true min, which is OK
    for us — we want to know if min_weight_H_2 ≥ d_X, so if even a
    capped search returns a small value, the hypothesis is dead).
    """
    if basis.size == 0:
        return 0
    k, _n = basis.shape
    best = basis.shape[1] + 1  # upper limit
    if cap is None:
        # Full enumeration.
        for mask in range(1, 1 << k):
            v = np.zeros(basis.shape[1], dtype=np.uint8)
            for i in range(k):
                if (mask >> i) & 1:
                    v ^= basis[i]
            w = int(v.sum())
            if 0 < w < best:
                best = w
        return best
    # Capped: subsets of size ≤ cap. Note this OVERESTIMATES the true min.
    for size in range(1, cap + 1):
        for subset in combinations(range(k), size):
            v = np.zeros(basis.shape[1], dtype=np.uint8)
            for i in subset:
                v ^= basis[i]
            w = int(v.sum())
            if 0 < w < best:
                best = w
                if best == 1:
                    return 1
    return best


def probe_instance(
    code_id: str, ell: int, m: int, A_str: str, B_str: str, d_X_true: int,
    enumerate_cap: int | None = None,
) -> KoszulProbeResult:
    G = ZmZn(ell, m)
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    M_A = circulant(A)
    M_B = circulant(B)

    basis_H2 = koszul_h2_basis(M_A, M_B)
    dim_H2 = basis_H2.shape[0]

    # Minimum weight in H_2 \ {0}.
    if dim_H2 == 0:
        min_weight = 0
    elif dim_H2 <= 16 and enumerate_cap is None:
        min_weight = min_weight_in_subspace(basis_H2)
    else:
        # Cap for tractability; report what we find. For k=6 (gross),
        # full enumeration is 2^6=64 — trivially full. For k=8 (bb_90,
        # bb_108) it's 256. For k=12 (bb_72, bb_288) it's 4096 — still
        # fast. Default unlimited.
        cap = enumerate_cap or 16
        min_weight = min_weight_in_subspace(basis_H2, cap=cap)

    # Ann(A), Ann(B) dimensions
    dim_ann_A = M_A.shape[1] - rank_f2(M_A)
    dim_ann_B = M_B.shape[1] - rank_f2(M_B)

    return KoszulProbeResult(
        code_id=code_id,
        ell=ell, m=m, G_order=G.cardinality,
        A_weight=A.weight(), B_weight=B.weight(),
        d_X_true=d_X_true,
        rank_M_A=rank_f2(M_A),
        rank_M_B=rank_f2(M_B),
        dim_H_2=dim_H2,
        min_weight_H_2=min_weight,
        dim_ann_A=dim_ann_A,
        dim_ann_B=dim_ann_B,
    )


def main() -> None:
    repo = Path(__file__).resolve().parents[1]
    table_path = repo / "instances" / "bravyi_table.yaml"
    with open(table_path) as f:
        data = yaml.safe_load(f)

    results: list[KoszulProbeResult] = []
    print(f"\n{'code_id':<22s} {'(n,k,d)':<12s} {'dim ann_A':>9s} {'dim ann_B':>9s}"
          f" {'dim H_2':>8s} {'minW(H_2)':>10s} {'d_X':>5s} {'gap':>5s} {'ratio':>6s}")
    print("─" * 100)
    for inst in data["instances"]:
        params = inst["parameters"]
        result = probe_instance(
            code_id=inst["code_id"],
            ell=inst["group"]["ell"],
            m=inst["group"]["m"],
            A_str=inst["polynomials"]["A"],
            B_str=inst["polynomials"]["B"],
            d_X_true=params["d"],
        )
        results.append(result)
        params_str = f"[[{params['n']},{params['k']},{params['d']}]]"
        print(
            f"{result.code_id:<22s} {params_str:<12s}"
            f" {result.dim_ann_A:>9d} {result.dim_ann_B:>9d}"
            f" {result.dim_H_2:>8d} {result.min_weight_H_2:>10d}"
            f" {result.d_X_true:>5d} {result.gap():>5d} {result.ratio():>6.2f}"
        )

    print("\nVerdict analysis:")
    print(f"  Bound 'd_X ≥ min weight in H_2' would hold iff gap ≥ 0 on every row.")
    tight_or_safe = sum(1 for r in results if r.gap() >= 0)
    print(f"    rows where bound holds: {tight_or_safe}/{len(results)}")
    if tight_or_safe < len(results):
        print(f"    FALSIFIED: H_2 minimum weight exceeds d_X on:")
        for r in results:
            if r.gap() < 0:
                print(f"      {r.code_id}: min_weight_H_2 = {r.min_weight_H_2} > d_X = {r.d_X_true}")
    else:
        print(f"    HOLDS on Bravyi table. Average tightness ratio: "
              f"{sum(r.ratio() for r in results) / len(results):.3f}")
        print(f"    Worst-case looseness (smallest ratio): "
              f"{min(r.ratio() for r in results):.3f}")


if __name__ == "__main__":
    main()

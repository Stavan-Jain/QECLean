"""Family D v3 — pin down the min_wt(H_2) = (4/9)|G| pattern (session 3).

Session 1 (family_d_v1_koszul_h2.py) observed empirically that for the 5
Bravyi instances, min_wt(H_2(Koszul(A,B))) = (4/9)·|G| exactly. Session 2
established the §6m obstruction theorem (min weight ≠ module invariant).

This session investigates the (4/9)|G| pattern structurally:

  1. Empirical verification on a broader corpus (~200-500 SAT-verified
     instances spanning all 17 group structures).
  2. Algebraic derivation: explain *why* the formula holds, factoring
     H_2 min-weight elements as products f(x)·g(y) ∈ F_2[Z_ℓ] ⊗ F_2[Z_m].
  3. Characterize the conditions under which the pattern holds and the
     exceptions (codes outside the "separable" family or with larger
     stabilizer subgroups).

Key insight from session-3 analysis:
  For BB codes (A, B) with A = A_x(x) + A_y(y) "x-y-separable"
  (each monomial purely in x or purely in y), and similarly for B,
  the joint annihilator H_2 = Ann(A) ∩ Ann(B) ⊃ Ann_x ⊗ Ann_y where:
    - Ann_x = {f ∈ F_2[Z_ℓ] : f·A_x = "match" AND f·B_x = "match"}
    - Ann_y = {g ∈ F_2[Z_m] : g·A_y = "match" AND g·B_y = "match"}

  Specifically, the "tensor element" f(x)·g(y) ∈ H_2 iff f and g satisfy
  the per-axis conditions enumerated in tensor_min_h2_conditions().

  Under the symmetric Bravyi-family structure (A = x^α + y^β + y^γ,
  B = y^δ + x^ε + x^ζ; both with one "pure" monomial in one axis
  and two in the other), the per-axis condition is "f fixed by x^α
  AND f killed by (1+x^ε+x^ζ)" which gives min weight (α-1)·(ℓ/α) when
  α | ℓ and (ε,ζ) reduce to "the residual cyclic" pattern.

This script:
  - Computes min_wt(H_2) for every SAT-verified instance.
  - Tests the (4/9)|G| equality (= ((wt-1)/wt)²·|G| for wt=3).
  - Characterizes exceptions.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path

import duckdb
import numpy as np

from bb_lab.checks import circulant
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly


@dataclass
class H2Probe:
    instance_id: str
    code_id: str
    ell: int
    m: int
    n: int
    k: int
    A_str: str
    B_str: str
    d_exact: int
    dim_H_2: int
    min_wt_H_2: int
    expected_4_9_G: float  # (4/9)·|G|
    matches: bool  # min_wt == (4/9)|G|, exactly

    @property
    def ratio_to_predicted(self) -> float:
        return self.min_wt_H_2 / self.expected_4_9_G if self.expected_4_9_G else float("nan")


def min_wt_H_2(M_A: np.ndarray, M_B: np.ndarray) -> tuple[int, int]:
    """Returns (dim_H_2, min_wt_H_2). Exact via brute force for dim ≤ 16."""
    stacked = np.concatenate([M_A, M_B], axis=0)
    basis = nullspace_f2(stacked)
    dim = basis.shape[0]
    if dim == 0:
        return 0, 0
    n = basis.shape[1]
    best = n + 1
    if dim <= 16:
        for mask in range(1, 1 << dim):
            v = np.zeros(n, dtype=np.uint8)
            for i in range(dim):
                if (mask >> i) & 1:
                    v ^= basis[i]
            w = int(v.sum())
            if 0 < w < best:
                best = w
        return dim, best
    # For larger dim, enumerate subsets of size up to 16.
    from itertools import combinations
    for size in range(1, 17):
        for subset in combinations(range(dim), size):
            v = np.zeros(n, dtype=np.uint8)
            for i in subset:
                v ^= basis[i]
            w = int(v.sum())
            if 0 < w < best:
                best = w
    return dim, best


def probe_row(row: tuple) -> H2Probe:
    (
        instance_id, code_id, ell, m, n, k, A_str, B_str, d_exact,
    ) = row
    G = ZmZn(ell, m)
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    M_A = circulant(A)
    M_B = circulant(B)
    dim_h2, min_wt = min_wt_H_2(M_A, M_B)
    expected = (4 * G.cardinality) / 9
    matches = (min_wt > 0) and (abs(min_wt - expected) < 1e-9)
    return H2Probe(
        instance_id=instance_id, code_id=code_id, ell=ell, m=m,
        n=n, k=k, A_str=A_str, B_str=B_str, d_exact=d_exact,
        dim_H_2=dim_h2, min_wt_H_2=min_wt, expected_4_9_G=expected,
        matches=matches,
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Family D v3 — pin down (4/9)|G| pattern in min_wt(H_2)."
    )
    parser.add_argument(
        "--limit", type=int, default=200,
        help="Number of corpus rows to probe (default: 200).",
    )
    parser.add_argument(
        "--all", action="store_true",
        help="Probe all SAT-verified corpus rows (~4,364).",
    )
    parser.add_argument(
        "--group", type=str, default=None,
        help="Restrict to a specific group structure (e.g. 'Z_12xZ_6').",
    )
    parser.add_argument(
        "--include-mixed", action="store_true",
        help="Include even mixed-axis polys (those with monomials like x*y).",
    )
    args = parser.parse_args()

    repo = Path(__file__).resolve().parents[1]
    db_path = repo / "data" / "bb_instances.duckdb"
    con = duckdb.connect(str(db_path), read_only=True)

    q = """
        SELECT instance_id, code_id, ell, m, n, k, A_poly, B_poly, d_exact
        FROM bb_instances
        WHERE d_exact IS NOT NULL
    """
    if args.group:
        # Parse 'Z_aXZ_b' style
        parts = args.group.replace("Z_", "").split("xZ_") if "xZ_" in args.group else args.group.replace("Z_", "").split("x")
        if len(parts) == 2:
            ell_q, m_q = int(parts[0]), int(parts[1])
            q += f" AND ell = {ell_q} AND m = {m_q}"
    q += " ORDER BY ell, m, instance_id"
    if args.all:
        rows = con.execute(q).fetchall()
    else:
        # Stratified sample: take some from each (ell, m).
        rows = con.execute(f"{q} LIMIT {args.limit * 10}").fetchall()
        # Sample uniformly across groups
        from collections import defaultdict
        by_group = defaultdict(list)
        for r in rows:
            by_group[(r[2], r[3])].append(r)
        per_group = max(1, args.limit // max(1, len(by_group)))
        rows = []
        for grp_rows in by_group.values():
            rows.extend(grp_rows[:per_group])
        rows = rows[:args.limit]

    print(f"Probing {len(rows)} SAT-verified BB code rows for (4/9)|G| pattern.\n")
    print(f"{'group':<14s} {'instance_id':<48s} {'|G|':>5s} {'k':>3s} {'d':>3s}"
          f" {'dimH2':>6s} {'minW':>5s} {'(4/9)|G|':>10s} {'match':>6s}")
    print("─" * 130)

    n_matches = 0
    n_total = 0
    n_mismatches_by_group: dict[tuple[int, int], int] = {}
    matches_by_group: dict[tuple[int, int], list[H2Probe]] = {}
    all_results: list[H2Probe] = []
    for row in rows:
        try:
            probe = probe_row(row)
        except Exception as exc:
            print(f"  ERROR on {row[0]}: {exc}")
            continue
        n_total += 1
        all_results.append(probe)
        grp = (probe.ell, probe.m)
        if probe.matches:
            n_matches += 1
        else:
            n_mismatches_by_group[grp] = n_mismatches_by_group.get(grp, 0) + 1
        matches_by_group.setdefault(grp, []).append(probe)

        # Verbose print for mismatches and first few of each group
        if not probe.matches or len(matches_by_group[grp]) <= 2:
            group_str = f"Z_{probe.ell}xZ_{probe.m}"
            match_str = "YES" if probe.matches else "no"
            print(f"{group_str:<14s} {probe.instance_id:<48s} {probe.n:>5d}"
                  f" {probe.k:>3d} {probe.d_exact:>3d}"
                  f" {probe.dim_H_2:>6d} {probe.min_wt_H_2:>5d}"
                  f" {probe.expected_4_9_G:>10.2f} {match_str:>6s}")

    print("\n" + "═" * 130)
    print(f"\nSUMMARY: {n_matches}/{n_total} instances match min_wt(H_2) = (4/9)·|G| EXACTLY")
    print(f"  Match rate: {n_matches/n_total*100:.2f}%")
    print()

    if n_mismatches_by_group:
        print("Mismatches by group structure:")
        for grp, cnt in sorted(n_mismatches_by_group.items()):
            total_in_grp = len(matches_by_group[grp])
            print(f"  Z_{grp[0]}xZ_{grp[1]}: {cnt}/{total_in_grp} mismatches")
        print("\nDetailed mismatches:")
        for probe in all_results:
            if not probe.matches:
                print(f"  {probe.instance_id} (Z_{probe.ell}xZ_{probe.m}, |G|={probe.n//2})")
                print(f"    A = {probe.A_str}, B = {probe.B_str}")
                print(f"    dim H_2 = {probe.dim_H_2}, min_wt = {probe.min_wt_H_2}, (4/9)|G| = {probe.expected_4_9_G}")

    # Match counts by group:
    print("\nMatch rates by group:")
    for grp in sorted(matches_by_group):
        probes = matches_by_group[grp]
        matches = sum(1 for p in probes if p.matches)
        print(f"  Z_{grp[0]}xZ_{grp[1]}: {matches}/{len(probes)} = {matches/len(probes)*100:.0f}%")


if __name__ == "__main__":
    main()

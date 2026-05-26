"""R4 (cross-orbit min weight) refinement test.

R4 replaces the C-v3 per-orbit `min_O w_1(A, O)` with cross-orbit
min weight:

    R4_A := min |f|_H  over  f ∈ ⊕_{O ∈ JointVan(A,B)} R_O  ∩  ker(M_A) \ {0}
    R4_B := symmetric for B
    bound_R4 := ⌈min(R4_A, R4_B) / c⌉

Tests on:
  - C1 (gross-style on Z_12 × Z_12): should give bound ≤ 12 = d.
  - gross (Z_12 × Z_6): should keep bound = 12 = d.
  - bb_288 (Z_12 × Z_12 with y^2 + y^7): should keep bound = 18 = d.
  - Sample T3-A violators (weight-4 Z_6 × Z_6): does R4 cover them?
  - Bravyi table: all 5 should remain consistent.

Parallelism on the T3-A sample via multiprocessing.Pool.

Run:
    uv run python scripts/tier3_cv3_r4_crossorbit.py
"""

from __future__ import annotations

import math
import multiprocessing as mp
import time
from dataclasses import dataclass

import numpy as np

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_depth,
)
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.degeneracy import is_g_odd_elementary_abelian
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    _min_weight_in_basis,
    bb_radical_bound,
    joint_support_subgroup_index,
    r_o_constraint_rows,
)
from bb_lab.sat_distance import x_distance


def joint_vanishing_orbit_indices(
    A: Poly, B: Poly, G: ZmZn
) -> list[int]:
    """Indices of orbits where both A and B vanish (μ_O > 0 for both)."""
    orbits = g_odd_frobenius_orbits(G)
    out = []
    for i, o in enumerate(orbits):
        if (jacobson_radical_depth(A, o, G) > 0
                and jacobson_radical_depth(B, o, G) > 0):
            out.append(i)
    return out


def cross_orbit_constraint_rows(
    G: ZmZn, joint_orbit_indices: list[int]
) -> np.ndarray:
    """F_2 rows pinning `v ∈ ⊕_{O ∈ joint} R_O ⊂ F_2[G]`.

    Equivalently: v's projection to R_{O'} is 0 for each O' NOT in
    `joint_orbit_indices`. Reuses `r_o_constraint_rows` per excluded
    orbit (which builds the per-fiber character constraints).

    For each excluded orbit O', we want v's R_{O'}-projection = 0. The
    function `r_o_constraint_rows(G, idx_in)` builds constraints
    "v ∈ R_{idx_in}", which means "v's projection to all other orbits is
    zero". So we need the *intersection* of "v ∉ R_{O'}" complements,
    which is just stacking the per-O' "projection to O' is zero" rows.
    """
    orbits = g_odd_frobenius_orbits(G)
    excluded = [i for i in range(len(orbits)) if i not in joint_orbit_indices]
    if not excluded:
        # No excluded orbits — every orbit is allowed. Empty constraint.
        return np.zeros((0, G.cardinality), dtype=np.uint8)
    # For each excluded orbit O', build the "projection to R_O' = 0" rows.
    # `r_o_constraint_rows(G, O_idx)` builds rows pinning v to R_{O_idx},
    # i.e., it constrains all OTHER orbits' projections to zero. So to
    # constrain just ONE orbit's projection, we need a different construction.
    # Build per-fiber per-character rows directly for the excluded orbits.
    # This mirrors the inner loop of `r_o_constraint_rows`.
    from bb_lab.radical_weight import (
        _chi_eval_f2,
        _orbit_size_from_rep,
        _reconstruct_g_from_odd_and_2,
        _g_index_table,
    )
    from bb_lab.algebraic_features import _g_odd_orders, _two_part_orders
    from itertools import product

    n_odds = _g_odd_orders(G)
    n_2s = _two_part_orders(G)
    g_index = _g_index_table(G)
    n_G = G.cardinality
    rows: list[np.ndarray] = []
    for excl_idx in excluded:
        rep = next(iter(orbits[excl_idx]))
        r_excl = _orbit_size_from_rep(rep, n_odds)
        for g_2 in product(*(range(n) for n in n_2s)):
            row_block = np.zeros((r_excl, n_G), dtype=np.uint8)
            for h_odd in product(*(range(n) for n in n_odds)):
                chi_val = _chi_eval_f2(rep, h_odd, n_odds)
                g = _reconstruct_g_from_odd_and_2(h_odd, g_2, n_odds, n_2s)
                col = g_index[g]
                for i in range(r_excl):
                    row_block[i, col] = chi_val[i]
            rows.append(row_block)
    if not rows:
        return np.zeros((0, n_G), dtype=np.uint8)
    return np.vstack(rows)


def r4_cross_orbit_bound(
    A: Poly, B: Poly, G: ZmZn,
    *, max_basis_dim: int = 22,
) -> tuple[int | float, dict]:
    """R4 bound (cross-orbit min over joint-vanishing orbits)."""
    joint_idx = joint_vanishing_orbit_indices(A, B, G)
    if not joint_idx:
        return 0, {"joint_vanishing_count": 0}
    cross_rows = cross_orbit_constraint_rows(G, joint_idx)
    M_A = circulant(A).astype(np.uint8)
    M_B = circulant(B).astype(np.uint8)

    def min_weight_with(M):
        blocks = [M]
        if cross_rows.shape[0] > 0:
            blocks.append(cross_rows)
        combined = np.vstack(blocks)
        basis = nullspace_f2(combined)
        if basis.shape[0] == 0:
            return float("inf"), 0
        if basis.shape[0] > max_basis_dim:
            return None, basis.shape[0]
        return _min_weight_in_basis(basis), basis.shape[0]

    minw_A, dim_A = min_weight_with(M_A)
    minw_B, dim_B = min_weight_with(M_B)
    info = {
        "joint_vanishing_count": len(joint_idx),
        "dim_A_subspace": dim_A,
        "dim_B_subspace": dim_B,
        "min_weight_A": minw_A,
        "min_weight_B": minw_B,
    }
    if minw_A is None or minw_B is None:
        info["error"] = f"basis dim too large (A: {dim_A}, B: {dim_B})"
        return None, info
    raw = min(minw_A, minw_B)
    if raw == float("inf"):
        return 0, info
    c = joint_support_subgroup_index(A, B, G)
    bound = math.ceil(raw / max(c, 1))
    info["c"] = c
    info["raw_min"] = raw
    return bound, info


# ---------------------------------------------------------------------------
# Single-case test with detailed report
# ---------------------------------------------------------------------------


@dataclass
class CaseResult:
    label: str
    G_label: str
    A: str
    B: str
    c: int
    elem_ab: bool
    n: int
    k: int
    bound_orig: int | float
    bound_r4: int | float | None
    d: int | None
    info: dict
    elapsed: float


def test_case(
    label: str, G: ZmZn, A_str: str, B_str: str,
    max_d: int = 12, skip_sat: bool = False,
) -> CaseResult:
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    t0 = time.time()
    checks = bb_check_matrices(A, B)
    params = code_params(checks)
    n, k = params.n, params.k
    bound_orig = bb_radical_bound(A, B, G)
    bound_r4, info = r4_cross_orbit_bound(A, B, G)
    c = joint_support_subgroup_index(A, B, G)
    elem_ab = is_g_odd_elementary_abelian(G)
    if skip_sat or k == 0:
        d = None
    else:
        try:
            res = x_distance(checks, weight_upper_bound=max_d)
            d = res.distance
        except Exception:
            d = None
    return CaseResult(
        label=label, G_label=G.label(),
        A=A_str, B=B_str, c=c, elem_ab=elem_ab,
        n=n, k=k, bound_orig=bound_orig, bound_r4=bound_r4,
        d=d, info=info, elapsed=time.time() - t0,
    )


# ---------------------------------------------------------------------------
# Worker for parallel T3-A violator sampling
# ---------------------------------------------------------------------------


@dataclass
class WorkSpec:
    idx: int
    ell: int
    m: int
    A_str: str
    B_str: str
    max_d: int


def _worker(spec: WorkSpec) -> dict:
    G = ZmZn(spec.ell, spec.m)
    A = Poly.from_string(spec.A_str, G)
    B = Poly.from_string(spec.B_str, G)
    bound_orig = bb_radical_bound(A, B, G)
    bound_r4, info = r4_cross_orbit_bound(A, B, G)
    try:
        res = x_distance(bb_check_matrices(A, B), weight_upper_bound=spec.max_d)
        d = res.distance
    except Exception:
        d = None
    return {
        "idx": spec.idx, "A": spec.A_str, "B": spec.B_str,
        "bound_orig": bound_orig, "bound_r4": bound_r4,
        "d": d, "info": info,
    }


def main():
    # Stage 1: the critical individual cases.
    print("=== Critical cases ===", flush=True)
    # tuples: (label, G, A_str, B_str, max_d, skip_sat, d_published)
    # bb_288 must skip SAT — its full distance proof is days of compute
    # (HANDOFF §6g). Use d_published = 18.
    cases = [
        ("gross on Z_12 × Z_6", ZmZn(12, 6),
         "x^3 + y + y^2", "y^3 + x + x^2", 12, False, 12),
        ("C1: gross-style on Z_12 × Z_12 (T3-C violator)", ZmZn(12, 12),
         "x^3 + y + y^2", "y^3 + x + x^2", 12, False, None),
        ("bb_288 on Z_12 × Z_12 (SAT skipped; using d_published)",
         ZmZn(12, 12), "x^3 + y^2 + y^7", "y^3 + x + x^2", 18, True, 18),
        ("bb_72 on Z_6 × Z_6", ZmZn(6, 6),
         "x^3 + y + y^2", "y^3 + x + x^2", 8, False, 6),
    ]
    for label, G, A_str, B_str, max_d, skip_sat, d_pub in cases:
        r = test_case(label, G, A_str, B_str, max_d=max_d, skip_sat=skip_sat)
        if r.d is None and d_pub is not None:
            r.d = d_pub  # use published value
        verdict_orig = "tight" if r.bound_orig == r.d else (
            "VIOLATION" if r.bound_orig is not None and r.d is not None
            and r.bound_orig > r.d else "loose"
        )
        verdict_r4 = "n/a"
        if r.bound_r4 is not None and r.d is not None:
            if r.bound_r4 > r.d:
                verdict_r4 = f"VIOLATES (R4 {r.bound_r4} > d {r.d})"
            elif r.bound_r4 == r.d:
                verdict_r4 = f"tight (R4 = d = {r.bound_r4})"
            else:
                verdict_r4 = f"loose (R4 {r.bound_r4} < d {r.d}, gap {r.d - r.bound_r4})"
        elif r.bound_r4 is None:
            verdict_r4 = (
                f"unable (dim {r.info.get('dim_A_subspace', '?')}, "
                f"{r.info.get('dim_B_subspace', '?')})"
            )
        print(f"\n  [{label}]")
        print(f"    n={r.n} k={r.k} c={r.c} d={r.d}")
        print(f"    C-v3 bound: {r.bound_orig} [{verdict_orig}]")
        print(f"    R4 bound:   {r.bound_r4} [{verdict_r4}]")
        info_compact = {k_: v for k_, v in r.info.items() if k_ != "error"}
        print(f"    R4 info:    {info_compact}")
        print(f"    ({r.elapsed:.1f}s)", flush=True)

    # Stage 2: T3-A violator sample (the 78 violators we collected).
    print("\n\n=== T3-A violator sample (parallel) ===")
    # Hard-coded sample of the 78 violators from /tmp/t3a_500.log.
    t3a_sample = [
        # weight-4 Z_6 × Z_6, all c=3, all elem-ab, A even-weight (excluded by R1).
        # Format: (A_str, B_str, max_d) — pick a small representative set.
        ("1 + y + y^2 + y^4", "1 + y^3 + x + x*y^3", 6),
        ("1 + y + y^2 + y^4", "1 + y^3 + x^2 + x^2*y^3", 6),
        ("1 + y + y^2 + y^4", "1 + y^3 + x^3 + x^3*y^3", 6),
        ("1 + y + y^2 + x", "1 + y^3 + x + x*y^3", 6),
        ("1 + y + y^2 + x", "1 + y^3 + x*y + x*y^4", 6),
        ("1 + y + y^2 + x", "1 + y^3 + x^2*y + x^3", 6),
        ("1 + y + y^2 + x", "1 + y^3 + x*y^3 + x^4", 6),
        ("1 + y + y^2 + x", "1 + x + x*y^3 + x^3", 6),
    ]
    specs = [
        WorkSpec(idx=i, ell=6, m=6, A_str=A, B_str=B, max_d=md)
        for i, (A, B, md) in enumerate(t3a_sample)
    ]
    with mp.Pool(processes=4) as pool:
        results = list(pool.imap_unordered(_worker, specs))
    results.sort(key=lambda r: r["idx"])
    print(f"  Tested {len(results)} weight-4 T3-A violators:")
    r4_saved = 0
    r4_still = 0
    r4_unable = 0
    for r in results:
        if r["d"] is None:
            verdict = "no SAT"
        elif r["bound_r4"] is None:
            verdict = "R4 unable"
            r4_unable += 1
        elif r["bound_r4"] > r["d"]:
            verdict = f"R4 {r['bound_r4']} > d {r['d']} — still violates"
            r4_still += 1
        elif r["bound_r4"] == r["d"]:
            verdict = f"R4 = d = {r['bound_r4']} (tight)"
            r4_saved += 1
        else:
            verdict = f"R4 {r['bound_r4']} < d {r['d']} (loose, gap {r['d'] - r['bound_r4']})"
            r4_saved += 1
        print(
            f"    A={r['A']!r:<32} B={r['B']!r:<40} "
            f"orig {r['bound_orig']} → R4 {r['bound_r4']} vs d {r['d']}: {verdict}"
        )
    print(
        f"\n  T3-A violator summary: {r4_saved} saved by R4, "
        f"{r4_still} still violate, {r4_unable} unable"
    )


if __name__ == "__main__":
    main()

"""Family D v1 — Koszul H_2 corpus check.

Companion to `family_d_v1_koszul_h2.py`. The seed check on the 5 Bravyi
instances showed `min_weight_H_2 > d_X` consistently (ratio 2.0-3.6).
This script extends the test to the full SAT-verified corpus.

Hypothesis to test:
    For all SAT-verified BB instances,  d_X ≤ min_weight_H_2.

Equivalently: H_2 (Ann(A) ∩ Ann(B)) is a "weight-thick" submodule that
never contains a vector lighter than d_X.

If this holds across the corpus, `min_weight_H_2` is a candidate
*upper* bound on d_X (NOT a lower bound). That's not directly useful
for a Family D lower bound, but suggests the *complementary* quantity
might be: see Phase 2 below.

Phase 1: empirical test on the corpus.
Phase 2: if Phase 1 holds, investigate `min weight in (Ann(A) ∪ Ann(B))`
        and `min weight in Ann(A)·Ann(B)` (which IS in the BB Z-codeword
        space).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import duckdb
import numpy as np

from bb_lab.checks import circulant
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly


@dataclass(frozen=True)
class CorpusRow:
    instance_id: str
    code_id: str
    ell: int
    m: int
    n: int
    k: int
    A_poly: str
    B_poly: str
    d_exact: int


def fetch_corpus(con: duckdb.DuckDBPyConnection, limit: int | None = None) -> list[CorpusRow]:
    q = """
        SELECT instance_id, code_id, ell, m, n, k, A_poly, B_poly, d_exact
        FROM bb_instances
        WHERE d_exact IS NOT NULL
        ORDER BY n, d_exact, instance_id
    """
    if limit is not None:
        q += f" LIMIT {limit}"
    rows = con.execute(q).fetchall()
    return [CorpusRow(*r) for r in rows]


def compute_min_weight_h2(
    A_str: str, B_str: str, ell: int, m: int, dim_limit: int = 16
) -> tuple[int, int]:
    """Compute (dim_H_2, min_weight_H_2) for a BB instance.

    `dim_limit` is the maximum dimension of H_2 we fully enumerate.
    For dim_H_2 ≤ dim_limit, we get the true minimum.
    For larger, we cap.
    """
    G = ZmZn(ell, m)
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    M_A = circulant(A)
    M_B = circulant(B)
    stacked = np.concatenate([M_A, M_B], axis=0)
    basis = nullspace_f2(stacked)
    dim_h2 = basis.shape[0]
    if dim_h2 == 0:
        return 0, 0

    # Enumerate min weight (full if dim ≤ dim_limit, else capped via random search)
    if dim_h2 <= dim_limit:
        min_w = basis.shape[1] + 1
        for mask in range(1, 1 << dim_h2):
            v = np.zeros(basis.shape[1], dtype=np.uint8)
            for i in range(dim_h2):
                if (mask >> i) & 1:
                    v ^= basis[i]
            w = int(v.sum())
            if w < min_w:
                min_w = w
                if min_w == 1:
                    return dim_h2, 1
        return dim_h2, min_w
    # Capped: enumerate subsets of size ≤ dim_limit (gives upper bound on true min,
    # since adding more basis vectors might decrease weight further).
    min_w = basis.shape[1] + 1
    # Just enumerate up to size dim_limit via combinations
    from itertools import combinations
    for size in range(1, dim_limit + 1):
        for subset in combinations(range(dim_h2), size):
            v = np.zeros(basis.shape[1], dtype=np.uint8)
            for i in subset:
                v ^= basis[i]
            w = int(v.sum())
            if w < min_w:
                min_w = w
                if min_w == 1:
                    return dim_h2, 1
    return dim_h2, min_w


def main() -> None:
    import sys
    repo = Path(__file__).resolve().parents[1]
    db_path = repo / "data" / "bb_instances.duckdb"
    con = duckdb.connect(str(db_path), read_only=True)

    # Sample 1: first 100 rows (small-n).
    rows = fetch_corpus(con, limit=None)
    print(f"\nProbing {len(rows)} SAT-verified corpus rows for min_weight_H_2 vs d_exact.", flush=True)
    print(f"{'instance_id':<45s} {'n':>4s} {'k':>3s} {'d':>3s} {'dimH2':>6s}"
          f" {'minW_H2':>8s} {'ratio':>6s} {'verdict':>10s}")
    print("─" * 110)

    n_loose = 0  # min_weight_H_2 < d_X (would BREAK the d_X ≤ min_wt_H_2 inequality)
    n_tight = 0  # == d_X
    n_strict_above = 0  # > d_X
    n_zero = 0
    n_total = 0
    ratios: list[float] = []
    min_ratio = float("inf")
    min_ratio_row: CorpusRow | None = None
    max_dim_seen = 0
    for row in rows:
        # Skip rows we can't compute cheaply.
        n_total += 1
        try:
            dim_h2, min_w = compute_min_weight_h2(
                row.A_poly, row.B_poly, row.ell, row.m, dim_limit=14,
            )
        except Exception as exc:
            print(f"  ERROR on {row.instance_id}: {exc}", flush=True)
            continue

        # Progress beacon every 50 rows.
        if n_total % 50 == 0:
            print(f"  ... processed {n_total} rows so far (n_loose={n_loose}, n_tight={n_tight}, max_dimH2={max_dim_seen})", flush=True)
        max_dim_seen = max(max_dim_seen, dim_h2)
        if dim_h2 == 0:
            n_zero += 1
            continue

        if min_w < row.d_exact:
            n_loose += 1
            verdict = "FALSIFIED"
            print(f"{row.instance_id:<45s} {row.n:>4d} {row.k:>3d} {row.d_exact:>3d}"
                  f" {dim_h2:>6d} {min_w:>8d} {min_w/row.d_exact:>6.2f} {verdict:>10s}")
        elif min_w == row.d_exact:
            n_tight += 1
            verdict = "tight"
        else:
            n_strict_above += 1
            verdict = "above"

        ratio = min_w / row.d_exact
        ratios.append(ratio)
        if ratio < min_ratio:
            min_ratio = ratio
            min_ratio_row = row

        # Verbose print only for sample
        if n_total <= 20 or row.code_id in {"bb_72_12_6", "bb_90_8_10", "bb_108_8_10", "gross", "bb_288_12_18"}:
            print(f"{row.instance_id:<45s} {row.n:>4d} {row.k:>3d} {row.d_exact:>3d}"
                  f" {dim_h2:>6d} {min_w:>8d} {ratio:>6.2f} {verdict:>10s}")

    print("\n─" * 110)
    print(f"Total processed: {n_total}, max dim_H_2 seen: {max_dim_seen}")
    print(f"  loose (min_wt_H_2 < d_X, would FALSIFY hypothesis): {n_loose}")
    print(f"  tight (= d_X): {n_tight}")
    print(f"  strict above (> d_X): {n_strict_above}")
    print(f"  H_2 = 0: {n_zero}")
    if ratios:
        avg = sum(ratios) / len(ratios)
        print(f"  avg ratio: {avg:.3f}")
        print(f"  min ratio: {min_ratio:.3f}")
        if min_ratio_row:
            print(f"    achieved by: {min_ratio_row.instance_id} (n={min_ratio_row.n}, d={min_ratio_row.d_exact})")

    if n_loose == 0:
        print("\nVERDICT: hypothesis HOLDS empirically across all checked rows.")
        print("  min_weight_H_2 is a candidate UPPER bound on d_X (or numerically ≥ d_X).")
        print("  For a LOWER bound, we need the COMPLEMENTARY direction.")
    else:
        print(f"\nVERDICT: hypothesis FAILS in {n_loose} rows.")


if __name__ == "__main__":
    main()

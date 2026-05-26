"""C-v1 numerical table on the gross [[144, 12, 12]] BB code.

Reproduces the (orbit, μ) → w_μ table for grossA and grossB
documented in `notes/Cv1_results.md` §3. Run with

    uv run python scripts/cv1_gross_table.py

Expected runtime: well under a second.
"""

from __future__ import annotations

import time

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_depth,
)
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import loewy_length, w_mu


def _format_value(v: int | float) -> str:
    if v == float("inf"):
        return "∞"
    return str(v)


def _print_table(poly_label: str, poly_str: str, G: ZmZn) -> None:
    A = Poly.from_string(poly_str, G)
    orbits = g_odd_frobenius_orbits(G)
    L = loewy_length(G)
    print(f"\n### {poly_label}: A = {poly_str}")
    header_cells = ["Orbit (rep)", "size", "μ_O"] + [
        f"w_{mu}" for mu in range(1, L + 1)
    ]
    print(" | ".join(header_cells))
    print(" | ".join(["---"] * len(header_cells)))
    for orb in orbits:
        rep = sorted(orb)[0]
        mu_O = jacobson_radical_depth(A, orb, G)
        values = [str(_format_value(w_mu(A, orb, mu, G))) for mu in range(1, L + 1)]
        row = [str(rep), str(len(orb)), str(mu_O)] + values
        print(" | ".join(row))


def main() -> None:
    G = ZmZn(12, 6)
    print("# C-v1 gross table (G = Z_12 × Z_6, Loewy length 5)")
    print(f"Loewy length: {loewy_length(G)}")
    t0 = time.time()
    _print_table("grossA", "x^3 + y + y^2", G)
    _print_table("grossB", "y^3 + x + x^2", G)
    print(f"\nTotal time: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()

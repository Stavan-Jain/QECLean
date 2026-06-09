"""A0 baseline scoreboard for the analytic-bound program.

For each of the 5 Bravyi-table instances, computes every quantity the
Phase-2 attack tracks measure themselves against:

  * classical single-block dual distances `d_A^⊥`, `d_B^⊥`
    (min weight in `ker(M_A)` / `ker(M_B)`)
  * the Lin–Pryadko degeneracy parameter `c = |G_a ∩ G_b|` and the
    Statement-12 bound `⌈min(d_A^⊥, d_B^⊥)/c⌉`
  * support-subgroup indices `[G : ⟨supp(A)⟩]`, `[G : ⟨supp(B)⟩]`
  * the full divisor lattice of base codes (SRB covers): for each
    base, `(ℓ', m')`, cover index `h`, parity (rigorous vs
    conjectural), base `(n, k)`, and base `d` where obtainable:
      - exact-match lookup against the Bravyi table itself,
      - SAT for small bases (`|G'| ≤ SAT_GROUP_CAP`),
      - L1-sampling upper bound otherwise (reported as `≤ w`, NOT a
        lower-bound input).

Run with

    uv run python scripts/analytic_baseline.py            # full (SAT on small bases)
    uv run python scripts/analytic_baseline.py --fast     # skip SAT, L1/lookup only

Output is the markdown body of `notes/A0_baseline.md` on stdout.
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

import yaml

from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.degeneracy import support_subgroup_index
from bb_lab.features import min_weight_in_kernel
from bb_lab.group import AbelianGroup, ZmZn
from bb_lab.homological_bounds import enumerate_base_codes
from bb_lab.l1_sampling import l1_distance_ub
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance
from bb_lab.weight_invariants import _intersection_subgroup_order, tz_lower_bound

SAT_GROUP_CAP = 24      # SAT exact d for base codes with |G'| ≤ this (n ≤ 48)
L1_SAMPLES = 50_000

BRAVYI_YAML = Path(__file__).resolve().parent.parent / "instances" / "bravyi_table.yaml"


def load_bravyi() -> list[dict]:
    with open(BRAVYI_YAML) as f:
        return yaml.safe_load(f)["instances"]


def build_table_lookup(instances: list[dict]):
    """Exact (supp A, supp B, orders) → d lookup over the Bravyi table."""
    lookup: dict[tuple[frozenset, frozenset, tuple[int, ...]], tuple[str, int]] = {}
    for inst in instances:
        G = ZmZn(inst["group"]["ell"], inst["group"]["m"])
        A = Poly.from_string(inst["polynomials"]["A"], G)
        B = Poly.from_string(inst["polynomials"]["B"], G)
        lookup[(A.support, B.support, G.orders)] = (
            inst["code_id"],
            inst["parameters"]["d"],
        )
    return lookup


def base_distance(
    A: Poly,
    B: Poly,
    G: AbelianGroup,
    table_lookup,
    *,
    fast: bool,
) -> tuple[str, str]:
    """Return (d_display, method) for a base code.

    d_display is exact (`"6"`), an upper bound (`"≤ 4"`), or `"?"`.
    """
    hit = table_lookup.get((A.support, B.support, G.orders))
    if hit is not None:
        code_id, d = hit
        return str(d), f"bravyi_table:{code_id}"

    checks = bb_check_matrices(A, B)
    params = code_params(checks)
    if params.k == 0:
        return "—", "k=0"

    ub: int | None = None
    try:
        ub = l1_distance_ub(checks, n_samples=L1_SAMPLES).distance_ub
    except ValueError:
        pass

    if not fast and G.cardinality <= SAT_GROUP_CAP:
        result = x_distance(checks, weight_upper_bound=ub)
        return str(result.distance), "sat"

    if ub is not None:
        return f"≤ {ub}", "l1_ub"
    return "?", "none"


def report_instance(inst: dict, table_lookup, *, fast: bool) -> None:
    code_id = inst["code_id"]
    ell, m = inst["group"]["ell"], inst["group"]["m"]
    G = ZmZn(ell, m)
    A = Poly.from_string(inst["polynomials"]["A"], G)
    B = Poly.from_string(inst["polynomials"]["B"], G)
    p = inst["parameters"]

    c = _intersection_subgroup_order(A.support, B.support, G)
    idx_A = support_subgroup_index(A, G)
    idx_B = support_subgroup_index(B, G)
    try:
        d_A_perp: int | str = min_weight_in_kernel(circulant(A))
        d_B_perp: int | str = min_weight_in_kernel(circulant(B))
        lp_line = (f"- Lin–Pryadko: c = {c}, bound = "
                   f"⌈min({d_A_perp},{d_B_perp})/{c}⌉ = "
                   f"**{tz_lower_bound(A, B, G)}** "
                   f"(gap to d: {p['d'] - tz_lower_bound(A, B, G)})")
    except ValueError as e:
        d_A_perp = d_B_perp = f"n/a ({e})"
        lp_line = f"- Lin–Pryadko: c = {c}, bound = n/a (kernel too large for brute force)"

    print(f"\n## {inst['display_name']} (`{code_id}`)")
    print()
    print(f"- G = Z_{ell} × Z_{m}, |G| = {G.cardinality};"
          f" A = `{inst['polynomials']['A']}`, B = `{inst['polynomials']['B']}`")
    print(f"- (n, k, d) = ({p['n']}, {p['k']}, {p['d']})  [table; d is SAT-established]")
    print(f"- d_A^⊥ = {d_A_perp}, d_B^⊥ = {d_B_perp}")
    print(lp_line)
    print(f"- support-subgroup indices: [G:⟨supp A⟩] = {idx_A}, [G:⟨supp B⟩] = {idx_B}")
    print()
    print("### Cover lattice (SRB base codes)")
    print()
    print("| ℓ′×m′ | h | parity | A′ | B′ | n′ | k′ | d′ (method) |")
    print("|---|---:|---|---|---|---:|---:|---|")
    for bc in sorted(enumerate_base_codes(A, B, G),
                     key=lambda b: (-b.G_base.cardinality, b.h)):
        checks = bb_check_matrices(bc.A_base, bc.B_base)
        params = code_params(checks)
        parity = "odd (rigorous)" if bc.is_rigorous else "even (conj.)"
        if params.k == 0:
            d_disp, method = "—", "k=0"
        else:
            d_disp, method = base_distance(
                bc.A_base, bc.B_base, bc.G_base, table_lookup, fast=fast)
        gl, gm = bc.G_base.orders
        print(f"| {gl}×{gm} | {bc.h} | {parity} "
              f"| `{bc.A_base.canonical_string()}` | `{bc.B_base.canonical_string()}` "
              f"| {params.n} | {params.k} | {d_disp} ({method}) |")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fast", action="store_true",
                        help="skip SAT on small bases; lookup + L1 only")
    args = parser.parse_args()

    instances = load_bravyi()
    table_lookup = build_table_lookup(instances)

    print("# A0 — analytic baseline scoreboard (Bravyi instances)")
    print()
    print(f"Generated by `scripts/analytic_baseline.py"
          f"{' --fast' if args.fast else ''}`.")
    print()
    print("Conventions: d′ exact unless prefixed `≤` (L1 sampling upper")
    print("bound — diagnostic only, never a lower-bound input). `parity`")
    print("says whether SRB Thm 4.7 applies rigorously (h odd) or only")
    print("the SRB §7 conjecture (h even).")

    t0 = time.time()
    for inst in instances:
        report_instance(inst, table_lookup, fast=args.fast)
    print(f"\n---\nTotal runtime: {time.time() - t0:.1f} s", file=sys.stderr)


if __name__ == "__main__":
    main()

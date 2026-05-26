"""T3-B/C/D/E spot-checks against the C-v3.1 REFINED hypothesis.

C-v3.1 refined hypothesis:
  * `is_g_odd_elementary_abelian(G)` (each prime-part of G_odd is elem-ab)
  * `c = [G_a : G_a ∩ G_b] >= 3`
  * `weight(A) odd  AND  weight(B) odd`  (= A(1) != 0, B(1) != 0 in F_2)

Claim under hypothesis:
    d_X(BB(G, A, B))  >=  ceil((1/c) * min_O min(w_1(A,O), w_1(B,O)))

Parallel SAT via multiprocessing.Pool. Run one battery at a time:

    uv run python scripts/tier3_cv3_refined_bcde.py --battery B
    uv run python scripts/tier3_cv3_refined_bcde.py --battery C
    uv run python scripts/tier3_cv3_refined_bcde.py --battery D
    uv run python scripts/tier3_cv3_refined_bcde.py --battery E
    uv run python scripts/tier3_cv3_refined_bcde.py --battery all
"""

from __future__ import annotations

import argparse
import multiprocessing as mp
import time
from dataclasses import dataclass

from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.degeneracy import is_g_odd_elementary_abelian
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    joint_support_subgroup_index,
)
from bb_lab.sat_distance import x_distance


def odd_weights(A: Poly, B: Poly) -> bool:
    return len(A.support) % 2 == 1 and len(B.support) % 2 == 1


def refined_in_domain(A: Poly, B: Poly, G: ZmZn) -> bool:
    if not is_g_odd_elementary_abelian(G):
        return False
    if joint_support_subgroup_index(A, B, G) < 3:
        return False
    return odd_weights(A, B)


@dataclass
class TestSpec:
    label: str
    ell: int
    m: int
    A_str: str
    B_str: str
    max_d: int


@dataclass
class TestResult:
    label: str
    G_label: str
    A_str: str
    B_str: str
    wA: int
    wB: int
    c: int
    elem_ab: bool
    in_domain: bool
    n: int
    k: int
    bound: int | None
    d: int | None
    verdict: str
    elapsed: float
    note: str = ""


def _worker(spec: TestSpec) -> TestResult:
    """Run one (G, A, B) spec. Each subprocess re-imports modules; fine
    since the import cost is amortized over a few SAT calls per worker."""
    G = ZmZn(spec.ell, spec.m)
    A = Poly.from_string(spec.A_str, G)
    B = Poly.from_string(spec.B_str, G)
    wA = len(A.support)
    wB = len(B.support)
    elem_ab = is_g_odd_elementary_abelian(G)
    c = joint_support_subgroup_index(A, B, G)
    in_domain = refined_in_domain(A, B, G)
    t0 = time.time()
    try:
        checks = bb_check_matrices(A, B)
        params = code_params(checks)
        n, k = params.n, params.k
    except Exception as e:
        return TestResult(
            label=spec.label, G_label=G.label(),
            A_str=spec.A_str, B_str=spec.B_str,
            wA=wA, wB=wB, c=c, elem_ab=elem_ab, in_domain=in_domain,
            n=-1, k=-1, bound=None, d=None,
            verdict="error",
            elapsed=time.time() - t0,
            note=f"code_params error: {e}",
        )
    if k == 0:
        return TestResult(
            label=spec.label, G_label=G.label(),
            A_str=spec.A_str, B_str=spec.B_str,
            wA=wA, wB=wB, c=c, elem_ab=elem_ab, in_domain=in_domain,
            n=n, k=0, bound=None, d=None,
            verdict="k=0",
            elapsed=time.time() - t0,
            note="k = 0; distance undefined",
        )
    bound = bb_radical_bound(A, B, G)
    try:
        res = x_distance(checks, weight_upper_bound=spec.max_d)
        d = res.distance
    except Exception as e:
        return TestResult(
            label=spec.label, G_label=G.label(),
            A_str=spec.A_str, B_str=spec.B_str,
            wA=wA, wB=wB, c=c, elem_ab=elem_ab, in_domain=in_domain,
            n=n, k=k, bound=bound, d=None,
            verdict="sat_error",
            elapsed=time.time() - t0,
            note=f"SAT error: {e}",
        )
    if not in_domain:
        verdict = "out"
    elif bound > d:
        verdict = "VIOLATION"
    elif bound == d:
        verdict = "tight"
    else:
        verdict = "loose"
    return TestResult(
        label=spec.label, G_label=G.label(),
        A_str=spec.A_str, B_str=spec.B_str,
        wA=wA, wB=wB, c=c, elem_ab=elem_ab, in_domain=in_domain,
        n=n, k=k, bound=bound, d=d,
        verdict=verdict,
        elapsed=time.time() - t0,
    )


def run_battery(name: str, specs: list[TestSpec], workers: int):
    print(f"\n=== {name} ===")
    t0 = time.time()
    if workers <= 1:
        results = [_worker(s) for s in specs]
    else:
        with mp.Pool(processes=workers) as pool:
            results = list(pool.imap_unordered(_worker, specs))
        # Restore order by label index.
        order = {s.label: i for i, s in enumerate(specs)}
        results.sort(key=lambda r: order[r.label])
    for r in results:
        line = (
            f"  [{r.label}] {r.G_label} A={r.A_str!r} B={r.B_str!r} "
            f"w=({r.wA},{r.wB}) c={r.c} elem_ab={r.elem_ab} "
            f"in_domain={r.in_domain}"
        )
        if r.d is not None:
            line += (
                f"  n={r.n} k={r.k} bound={r.bound} d={r.d} "
                f"[{r.verdict}] ({r.elapsed:.1f}s)"
            )
        elif r.note:
            line += f"  {r.note} ({r.elapsed:.1f}s)"
        print(line)
    in_domain = [r for r in results if r.in_domain and r.d is not None]
    vios = [r for r in in_domain if r.verdict == "VIOLATION"]
    tight = [r for r in in_domain if r.verdict == "tight"]
    loose = [r for r in in_domain if r.verdict == "loose"]
    print(
        f"  Battery summary ({time.time()-t0:.1f}s): "
        f"{len(in_domain)} in-domain, {len(vios)} viol, "
        f"{len(tight)} tight, {len(loose)} loose"
    )
    return vios


# ---------------------------------------------------------------------------
# Battery T3-B: other G_odd primes (Z_5×Z_5, Z_7×Z_7, Z_3×Z_5)
# ---------------------------------------------------------------------------

T3_B = [
    TestSpec("B1: Z_5×Z_5 x-only/y-only w3",
             5, 5, "1 + x + x^2", "1 + y + y^2", 6),
    TestSpec("B2: Z_5×Z_5 w3 weight-3 with mix",
             5, 5, "1 + x + x^2", "1 + y + x*y", 6),
    TestSpec("B3: Z_5×Z_5 w3 x²/y²",
             5, 5, "1 + x + x^3", "1 + y + y^3", 6),
    TestSpec("B4: Z_7×Z_7 x-only/y-only w3",
             7, 7, "1 + x + x^2", "1 + y + y^2", 8),
    TestSpec("B5: Z_7×Z_7 w3 alt",
             7, 7, "1 + x + x^3", "1 + y + y^3", 8),
    TestSpec("B6: Z_3×Z_5 w3",
             3, 5, "1 + x + x^2", "1 + y + y^2", 6),
    TestSpec("B7: Z_3×Z_7 w3",
             3, 7, "1 + x + x^2", "1 + y + y^2", 6),
]


# ---------------------------------------------------------------------------
# Battery T3-C: larger G_2 structure
# ---------------------------------------------------------------------------

T3_C = [
    TestSpec("C1: Z_12×Z_12 gross-style w3",
             12, 12, "x^3 + y + y^2", "y^3 + x + x^2", 12),
    TestSpec("C2: Z_12×Z_12 a=4",
             12, 12, "x^4 + y + y^2", "y^4 + x + x^2", 12),
    TestSpec("C3: Z_8×Z_6 rank-1 G_odd w3",
             8, 6, "1 + y + y^2", "x + x^2 + x^3", 8),
    TestSpec("C4: Z_8×Z_6 w3 cross",
             8, 6, "x + y + y^2", "x^2 + x*y + x^2*y", 8),
    TestSpec("C5: Z_16×Z_6 w3",
             16, 6, "x^4 + y + y^2", "y^3 + x + x^2", 10),
    TestSpec("C6: Z_24×Z_6 gross-style w3",
             24, 6, "x^3 + y + y^2", "y^3 + x + x^2", 10),
]


# ---------------------------------------------------------------------------
# Battery T3-D: adversarial natural-construction tests
# ---------------------------------------------------------------------------

T3_D = [
    TestSpec("D1: Z_6×Z_6 gross-like A,B",
             6, 6, "x^3 + y + y^2", "y^3 + x + x^2", 8),
    TestSpec("D2: Z_6×Z_6 A=swap(B)-style",
             6, 6, "1 + x + y^2", "1 + y + x^2", 8),
    TestSpec("D3: Z_6×Z_6 high-c case",
             6, 6, "1 + x + x^2", "1 + y + y^2", 8),
    TestSpec("D4: Z_6×Z_6 deg-aligned",
             6, 6, "1 + x^2 + y^4", "1 + y^2 + x^4", 8),
    TestSpec("D5: Z_6×Z_6 cross-axis",
             6, 6, "1 + x + x*y", "1 + y + x*y", 8),
    TestSpec("D6: Z_4×Z_6 rank-1 G_odd",
             4, 6, "1 + y + y^2", "x + x*y + x*y^2", 8),
]


# ---------------------------------------------------------------------------
# Battery T3-E: gross-family parametric scan
# ---------------------------------------------------------------------------

T3_E = [
    TestSpec("E1: gross itself",
             12, 6, "x^3 + y + y^2", "y^3 + x + x^2", 12),
    TestSpec("E2: Z_12×Z_6 a=2",
             12, 6, "x^2 + y + y^2", "y^3 + x + x^2", 12),
    TestSpec("E3: Z_12×Z_6 a=4",
             12, 6, "x^4 + y + y^2", "y^3 + x + x^2", 12),
    TestSpec("E4: Z_12×Z_6 a=6",
             12, 6, "x^6 + y + y^2", "y^3 + x + x^2", 12),
    TestSpec("E5: Z_12×Z_6 a=9",
             12, 6, "x^9 + y + y^2", "y^3 + x + x^2", 12),
    TestSpec("E6: Z_12×Z_6 reordered y exps",
             12, 6, "x^3 + y^2 + y^5", "y^3 + x + x^2", 12),
]


BATTERIES = {
    "B": ("T3-B: other G_odd primes", T3_B),
    "C": ("T3-C: larger G_2 structure", T3_C),
    "D": ("T3-D: adversarial natural constructions", T3_D),
    "E": ("T3-E: gross-family parametric scan", T3_E),
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--battery", default="B",
                    help="One of: B, C, D, E, all")
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()
    targets = (
        list(BATTERIES.keys()) if args.battery == "all"
        else [args.battery]
    )
    all_vios = []
    for key in targets:
        name, specs = BATTERIES[key]
        all_vios += run_battery(name, specs, workers=args.workers)
    print("\n=== Overall ===")
    if all_vios:
        print(f"  Total violations across batteries: {len(all_vios)}")
        for v in all_vios:
            print(
                f"  - {v.label} {v.G_label} A={v.A_str!r} B={v.B_str!r}: "
                f"bound={v.bound} > d={v.d}"
            )
    else:
        print(f"  No violations across battery {args.battery}.")


if __name__ == "__main__":
    main()

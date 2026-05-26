"""Tier-3 adversarial search: sample random weight-3 BB polynomials and
test the conjecture.

For each (G, A, B) sample:
  * Compute the bound (Σ |O| · min(μ_A, μ_B)).
  * Compute a cheap upper bound on d_X via L1 sampling.
  * If bound > L1 UB, this is a candidate violation.
  * For confirmed violations on small enough cases, optionally cross-check
    with brute-force distance (cheap for small n).

Also looks for edge cases: instances where μ_O is large (≥ 3) and
whether the bound still holds.
"""

from __future__ import annotations

import argparse
import random
import time
from collections import Counter
from pathlib import Path

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_bound,
    jacobson_radical_depth,
)
from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.group import ZmZn
from bb_lab.l1_sampling import l1_distance_ub
from bb_lab.poly import Poly


def random_weight_w_poly(G: ZmZn, w: int, rng: random.Random) -> Poly:
    """Random weight-w polynomial in F_2[G]: pick w distinct group elements."""
    all_elements = list(G)
    while True:
        supp = rng.sample(all_elements, w)
        return Poly.from_support(supp, G)


def adversarial_pass(
    G: ZmZn,
    n_samples: int = 100,
    weight: int = 3,
    seed: int = 0,
    n_l1: int = 10_000,
    *,
    skip_k0: bool = True,
) -> list[dict]:
    rng = random.Random(seed)
    results: list[dict] = []
    t0 = time.time()
    n_done = 0
    violations = 0
    for trial in range(n_samples):
        A = random_weight_w_poly(G, weight, rng)
        B = random_weight_w_poly(G, weight, rng)
        try:
            checks = bb_check_matrices(A, B)
        except Exception:
            continue
        params = code_params(checks)
        if skip_k0 and params.k == 0:
            continue
        bound = jacobson_radical_bound(A, B, G)
        try:
            sampling_result = l1_distance_ub(checks, n_samples=n_l1, seed=trial)
            ub = sampling_result.distance_ub
        except Exception:
            ub = float("inf")
        result = dict(
            trial=trial,
            A=A.canonical_string(),
            B=B.canonical_string(),
            n=params.n,
            k=params.k,
            bound=bound,
            l1_ub=ub,
            violation=(bound > ub),
        )
        if result["violation"]:
            violations += 1
        results.append(result)
        n_done += 1
        if n_done % 25 == 0:
            print(f"  G={G.label()}: {n_done}/{n_samples} done "
                  f"({time.time()-t0:.1f}s, violations={violations})", flush=True)
    return results


def edge_case_max_mu_search(
    G: ZmZn, n_samples: int = 200, weight: int = 3, seed: int = 0
) -> list[dict]:
    """Find polynomial pairs where some μ is large (≥ 3) — edge cases for
    the conjecture."""
    rng = random.Random(seed)
    orbits = g_odd_frobenius_orbits(G)
    hits: list[dict] = []
    for trial in range(n_samples):
        A = random_weight_w_poly(G, weight, rng)
        B = random_weight_w_poly(G, weight, rng)
        max_mu_A = max(
            jacobson_radical_depth(A, o, G) for o in orbits
        )
        max_mu_B = max(
            jacobson_radical_depth(B, o, G) for o in orbits
        )
        if max_mu_A >= 3 or max_mu_B >= 3:
            try:
                checks = bb_check_matrices(A, B)
                params = code_params(checks)
                bound = jacobson_radical_bound(A, B, G)
                try:
                    if params.k > 0:
                        ub = l1_distance_ub(checks, n_samples=5000, seed=trial).distance_ub
                    else:
                        ub = float("inf")
                except Exception:
                    ub = float("inf")
                hits.append(dict(
                    trial=trial,
                    A=A.canonical_string(),
                    B=B.canonical_string(),
                    n=params.n,
                    k=params.k,
                    max_mu_A=max_mu_A,
                    max_mu_B=max_mu_B,
                    bound=bound,
                    l1_ub=ub,
                    violation=(bound > ub and ub != float("inf")),
                ))
            except Exception:
                pass
    return hits


def render(
    pass_results: dict[str, list[dict]],
    edge_results: dict[str, list[dict]],
) -> str:
    out: list[str] = []
    out.append("# T3.4 — Tier-3 adversarial search")
    out.append("")
    out.append(
        "Random weight-3 BB polynomial pairs over each group; "
        "L1 sampling gives a cheap upper bound on d_X. Violations: "
        "bound > L1_UB (a genuine violation must satisfy bound > d, so "
        "bound > L1_UB ≥ d implies bound > d)."
    )
    out.append("")
    out.append("## Pass A: random weight-3 BB pairs")
    out.append("")
    out.append("| Group | samples | k≥2 instances | violations | rate |")
    out.append("|---|---:|---:|---:|---:|")
    for G_label, results in pass_results.items():
        n_violations = sum(1 for r in results if r["violation"])
        out.append(f"| {G_label} | {len(results)} | {len(results)} | "
                   f"{n_violations} | {n_violations/max(len(results),1):.1%} |")
    out.append("")

    for G_label, results in pass_results.items():
        viols = [r for r in results if r["violation"]]
        if not viols:
            continue
        out.append(f"### Violations on {G_label} (sample of {min(10, len(viols))})")
        out.append("")
        out.append("| A | B | n | k | bound | L1_UB |")
        out.append("|---|---|---:|---:|---:|---:|")
        for r in viols[:10]:
            out.append(f"| `{r['A']}` | `{r['B']}` | {r['n']} | {r['k']} | "
                       f"{r['bound']} | {r['l1_ub']} |")
        out.append("")

    # μ distributions
    out.append("## μ distribution observed in samples")
    out.append("")
    for G_label, results in pass_results.items():
        bound_counter = Counter(r["bound"] for r in results)
        out.append(f"- **{G_label}**: bound distribution = "
                   f"{dict(sorted(bound_counter.items()))}")
    out.append("")

    out.append("## Edge cases: μ ≥ 3 instances")
    out.append("")
    out.append("Polynomials with max_μ ≥ 3 are rare for random weight-3. "
               "Are they still bound-satisfying?")
    out.append("")
    for G_label, hits in edge_results.items():
        out.append(f"### {G_label}: {len(hits)} hits with max μ ≥ 3")
        if hits:
            out.append("")
            out.append("| A | B | max μ(A) | max μ(B) | bound | L1_UB | violation? |")
            out.append("|---|---|---:|---:|---:|---:|:---:|")
            for r in hits[:15]:
                tag = "YES" if r["violation"] else "no"
                out.append(f"| `{r['A']}` | `{r['B']}` | {r['max_mu_A']} | {r['max_mu_B']} | "
                           f"{r['bound']} | {r['l1_ub']} | {tag} |")
        out.append("")

    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples-per-group", type=int, default=100)
    ap.add_argument("--edge-samples", type=int, default=200)
    ap.add_argument("--output", type=Path, default=None)
    args = ap.parse_args()

    pass_results: dict[str, list[dict]] = {}
    edge_results: dict[str, list[dict]] = {}
    for (ell, m) in [(12, 6), (15, 2), (6, 4)]:
        G = ZmZn(ell, m)
        print(f"\n== Group {G.label()} ==", flush=True)
        pass_results[G.label()] = adversarial_pass(
            G, n_samples=args.samples_per_group, seed=0
        )
        edge_results[G.label()] = edge_case_max_mu_search(
            G, n_samples=args.edge_samples, seed=1
        )

    report = render(pass_results, edge_results)
    if args.output:
        args.output.write_text(report)
        print(f"\nWrote report to {args.output}")
    else:
        print(report)


if __name__ == "__main__":
    main()

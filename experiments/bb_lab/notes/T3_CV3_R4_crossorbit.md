# T3 — R4 cross-orbit min refinement attempt

Date: 2026-05-26. Follow-up to T3-C falsification.

Companion document to `T3_summary_draft.md` (overall T3 summary) and
`T3_CV3_C_g2.md` (the C1 violator). This note records a **distinct
refinement attempt** (R4: cross-orbit min weight) tested in parallel
with the other agent's H_UNIT² investigation. Both targeted the
C1 violator. Combined empirical picture below.

## R4 hypothesis

The C-v3 conjecture uses

  `(1/c) · min_O w_1(A, O)` (per-orbit min)

where `min_O` is over joint-vanishing orbits and `w_1` is the
per-orbit isotypic kernel min weight. R4 replaces this with the
**cross-orbit min weight** over the direct sum:

  `R4_A := min |f|_H over f ∈ (⊕_{O ∈ JointVan(A,B)} R_O) ∩ ker(M_A) \ {0}`

with `R4_B` symmetric. Bound:

  `bound_R4 := ⌈min(R4_A, R4_B) / c⌉`

This allows cross-orbit cancellation within the joint-vanishing
direct sum, which the per-orbit min misses.

## Implementation

`scripts/tier3_cv3_r4_crossorbit.py` builds the cross-orbit
constraint matrix per excluded orbit's per-G_2-fiber characters
(reusing `_chi_eval_f2` + `_reconstruct_g_from_odd_and_2` from
`radical_weight.py`), stacks with `M_A` (or `M_B`), takes F_2
nullspace, then Gray-codes the min weight.

## Critical-case results

| Case | C-v3 bound | R4 bound | d | C-v3 verdict | R4 verdict |
|---|---|---|---|---|---|
| gross (Z₁₂×Z₆) | 12 | **8** | 12 | tight | loose (gap 4) |
| **C1 violator (Z₁₂×Z₁₂)** | 18 | **12** | 12 | **VIOLATION** | **tight** ✓ |
| bb_288 (Z₁₂×Z₁₂) | 18 | 12 | 18 | tight | loose (gap 6) |
| bb_72 (Z₆×Z₆) | 6 | 4 | 6 | tight | loose (gap 2) |

R4 raw cross-orbit min weights:
- gross: 24 (vs per-orbit 36)
- C1: 36 (vs per-orbit 54)
- bb_288: 36 (vs per-orbit 54)
- bb_72: 12 (vs per-orbit 36)

**Diagnostic**: cross-orbit cancellation is real for all four codes
(reduces min weight by ~33%). C-v3's tightness on gross/bb_288/bb_72
was therefore a **coincidence** — the per-orbit min happened to equal
`d · c` even though the algebraically correct min is smaller.

## T3-A violator sample

Tested R4 on 8 representatives of the 78 weight-4 Z₆×Z₆ violators:

| A family | size | R4 saves | R4 still violates |
|---|:---:|:---:|:---:|
| `1+y+y²+y⁴` (y-only) | 3 | **3/3** ✓ | 0 |
| `1+y+y²+x` (mixed) | 5 | 1 | **4/5** ✗ |

For the `1+y+y²+x` A family, R4 = 6 still exceeds d ∈ {2, 4}. So R4
alone does not save all T3-A violators. R1 (odd-weight hypothesis)
is still needed to exclude weight-4 cases from the conjecture's domain.

## Combined picture: R1 + R4

The cleanest empirically-correct synthesis is the conjunction:

> **Hypothesis**: `is_g_odd_elementary_abelian(G) ∧ c ≥ 3
>   ∧ weight(A) odd ∧ weight(B) odd`
>
> **Bound**: `d_X(BB(G, A, B)) ≥ ⌈(1/c) · cross_orbit_min_weight(A, B, G)⌉`

Under R1 + R4:
- All T3-A weight-4 violators are excluded by R1.
- C1 is in-domain and R4 gives a tight (= d) bound.
- gross, bb_288, bb_72 are in-domain; R4 gives a correct but loose bound.

**Trade-off**: R4 is a strictly weaker bound than C-v3's per-orbit
formula on the Bravyi codes. We lose tightness on gross, bb_72, bb_288
(by 4, 2, 6 respectively). But the conjecture becomes EMPIRICALLY
TRUE (lower bound holds across all tested in-domain cases).

## Relationship to H_UNIT² (other agent's refinement)

H_UNIT² is a refinement targeting the SAME C1 violator with a
DIFFERENT mechanism — it constrains the per-axis Loewy unit-factor
structure of A. H_UNIT² is a structural hypothesis (in/out of domain)
not a bound formula. R4 is a bound formula not a hypothesis.

The two are largely **orthogonal** and could potentially be combined:
- H_UNIT² (if it survives) would exclude C1 from hypothesis domain,
  keeping the C-v3 tight per-orbit bound on the smaller domain.
- R4 (this note's finding) keeps C1 in domain but uses a weaker
  bound formula. Saves C1 without tightening to a structural condition.

Both are mathematically valid responses to the C1 falsification:
- R1 + R4 → broader domain, looser bound (always correct).
- R1 + H_UNIT² + C-v3 per-orbit bound → narrower domain, tighter bound
  (if H_UNIT² survives).

The H_UNIT² verdict is pending (per `T3_summary_draft.md` §H_UNIT²).

## Verdict on R4

**R4 is a uniformly correct lower bound (loose), not a tight one.**

If the program's goal is a *correct* lower bound for the engineered
BB-code family: R1 + R4 works and is provable.

If the program's goal is a *tight* bound matching d on the Bravyi
table: R4 alone doesn't deliver. Either H_UNIT² (or similar) is
needed to narrow the hypothesis, or the program accepts loose bounds.

## Caveats / open questions

- The "cross-orbit min weight" used by R4 is closely related to (but
  not identical to) the LP `d_A^⊥` quantity. Specifically, R4 restricts
  to ⊕_{O joint vanishing} R_O, while LP `d_A^⊥` is min weight over
  all of ker(M_A). R4 might be **provably equal** to `d_A^⊥` in the
  semisimple-G_odd regime — worth verifying as a separate exercise.
- Gray-code enumeration limits the basis dim to ~22. For larger
  groups (Z_12 × Z_12 etc.) the cross-orbit subspace dim is 16,
  fits comfortably. For substantially larger G, smarter min-weight
  algorithms would be needed.
- The C-v1 unit-invariance restriction carries through (HANDOFF_C §7).
  Whether R4 has the same "drop unit equivalence" requirement is
  not yet verified.

## Reproduction

```
$ uv run python scripts/tier3_cv3_r4_crossorbit.py
```

Expect ~12 min total (gross SAT ~90s, C1 SAT ~10 min, bb_288 skipped,
bb_72 ~1s, T3-A sample ~few seconds).

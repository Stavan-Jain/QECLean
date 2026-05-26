# Evidence — Tier 3 falsification of C-v3

## T3-A: Weight-4 BB codes over Z_6 × Z_6

**Falsified with 78 violators / 500 in-scope (15.6% rate).**

Reproduce:

    cd experiments/bb_lab
    uv run python scripts/tier3_cv3_a_weight4.py --limit 500 --max-d 10

Top observation: violators concentrate on two A polynomials,
both even-weight 4:

| violator A | count |
|---|:---:|
| `1 + y + y² + x` | 65 |
| `1 + y + y² + y⁴` | 13 |

**Refinement R1 (odd-weight)** saves all 78. Verified via:

    uv run python scripts/tier3_cv3_refinement_test.py --limit 500

R1 results: 78/78 violators excluded by adding "weight(A), weight(B)
both odd" to the hypothesis. R2 (skip-trivial-orbit) gives 0/78 saves
(diagnostically: 65 vacuous, 13 still violate).

→ C-v3.1 = C-v3 ∧ R1 survives T3-A.

## T3-B: Other G_odd primes

**Inconclusive — most cases had k = 0.**

Reproduce:

    uv run python scripts/tier3_cv3_refined_bcde.py --battery B

| label | G | A | B | k | bound | d | verdict |
|---|---|---|---|---|---|---|---|
| B1 | Z_5×Z_5 | 1+x+x² | 1+y+y² | 0 | — | — | k=0 |
| B4 | Z_7×Z_7 | 1+x+x² | 1+y+y² | 0 | — | — | k=0 |
| **B5** | Z_7×Z_7 | 1+x+x³ | 1+y+y³ | 18 | 4 | 4 | **tight** |
| ... | ... | ... | ... | 0 | — | — | k=0 |

One in-domain k>0 case (B5), tight. No violations, but limited
testable evidence. p=3-dependent failure modes not ruled out.

## T3-C: Larger G_2 (the decisive falsifier)

**Falsified with C1: Z_12 × Z_12 gross-style polys**.

Reproduce:

    uv run python scripts/tier3_cv3_refined_bcde.py --battery C

| label | G | A | B | c | k | bound | d | verdict |
|---|---|---|---|---|---|---|---|---|
| **C1** | Z_12×Z_12 | x³+y+y² | y³+x+x² | 3 | 16 | 18 | **12** | **VIOLATION** |
| C2 | Z_12×Z_12 | x⁴+y+y² | y⁴+x+x² | 4 | 0 | — | — | k=0 |
| C3-C5 | various | various | various | various | 0 | — | — | k=0 |
| C6 | Z_24×Z_6 | x³+y+y² | y³+x+x² | 3 | 16 | 18 | (SAT timeout @ w=10) | — |

C1 is **in-domain under C-v3.1** (all hypothesis clauses hold:
elem-ab G_odd, c=3, odd weights). The bound overshoots d by 6.

**Critical observation**: w_1 = 54 for both C1 and bb_288 on
Z_12 × Z_12 (= same A polynomial structurally produces same w_1).
But d_C1 = 12 ≠ d_bb288 = 18. So C-v1's w_1 cannot distinguish
these polynomials, even though their BB-code distances differ.

→ C-v3.1 falsified. Refinement attempt H_UNIT² tested in §H_UNIT²
below.

## T3-D: Adversarial natural constructions

**Clean — 0 violations / 2 in-domain.**

Reproduce:

    uv run python scripts/tier3_cv3_refined_bcde.py --battery D

| label | G | A | B | c | in_dom | bound | d | verdict |
|---|---|---|---|---|---|---|---|---|
| D1 | Z_6×Z_6 | x³+y+y² | y³+x+x² | 3 | ✓ | 6 | 6 | tight |
| D3 | Z_6×Z_6 | 1+x+x² | 1+y+y² | 6 | ✓ | 2 | 4 | loose |
| D2, D4-D6 | various | — | — | <3 | ✗ | — | — | out |

Full hill-climb adversarial sampler not run; small hand-picked set only.

## T3-E: Bravyi-family parametric scan

**Clean — 0 violations / 3 in-domain testable.**

Reproduce:

    uv run python scripts/tier3_cv3_refined_bcde.py --battery E

| label | G | A | B | k | bound | d | verdict |
|---|---|---|---|---|---|---|---|
| E1 (gross) | Z_12×Z_6 | x³+y+y² | y³+x+x² | 12 | 12 | 12 | **tight** |
| E2 | Z_12×Z_6 | x²+y+y² | y³+x+x² | 0 | — | — | k=0 |
| E4 | Z_12×Z_6 | x⁶+y+y² | y³+x+x² | 8 | 6 | 6 | **tight** |
| E5 | Z_12×Z_6 | x⁹+y+y² | y³+x+x² | 12 | 12 | 12 | **tight** |

Confirms the conjecture survives within gross's polynomial-family
parameter space on its native group.

## H_UNIT² refinement attempt (FAILED)

Tested whether requiring "A's per-axis Loewy unit factor squares to 1"
fixes the T3-C falsifier. Per HANDOFF_TIER3_CV3 §6 "single
counterexample suffices to falsify."

Reproduce:

    uv run python scripts/tier3_cv3_unit_squared_targeted.py --workers 6 --cap 13

Test set: 6 hand-picked (b, c) pairs with `{b mod 3, c mod 3} = {1, 2}`
to ensure k > 0 jointly with B = y³+x+x², covering both
H_UNIT² ✓ and ✗ signatures.

Completed results:

| case | mod-4 sig | predicted | actual | verdict |
|---|---|---|---|---|
| C1 (1, 2) | (1, 2) | ✗ → viol | ✓ matches | VIOLATION |
| (5, 10) | (1, 2) | ✗ → viol | ✓ matches | VIOLATION |
| (1, 11) | (1, 3) | ✓ → tight | ✓ matches | tight |
| **(4, 5)** | **(0, 1)** | **✓ → tight** | **✗ FAILS** | **VIOLATION** |
| bb_288 (2, 7) | (2, 3) | ✓ → tight | (heroic SAT pending) | tight (expected) |
| (4, 11) | (0, 3) | ✗ → viol | (pending) | (expected VIOLATION) |

**(4, 5) refutes H_UNIT²**: y-axis-only Loewy polynomial is bare `y'`
(no unit factor, u = 1, u² = 1 trivially → H_UNIT² ✓ predicts tight),
but BB-code d = 12 < bound = 18 → VIOLATION.

See [`T3_CV3_H_UNIT2_attempt.md`](../../experiments/bb_lab/notes/T3_CV3_H_UNIT2_attempt.md)
for full diagnosis.

## Reproducibility summary

```
cd experiments/bb_lab

# T3-A:
uv run python scripts/tier3_cv3_a_weight4.py --limit 500 --max-d 10

# T3-A refinement test (R1/R2 vs 78 violators):
uv run python scripts/tier3_cv3_refinement_test.py --limit 500

# T3-B/C/D/E spot-checks:
uv run python scripts/tier3_cv3_refined_bcde.py --battery B
uv run python scripts/tier3_cv3_refined_bcde.py --battery C
uv run python scripts/tier3_cv3_refined_bcde.py --battery D
uv run python scripts/tier3_cv3_refined_bcde.py --battery E

# H_UNIT² attempt:
uv run python scripts/tier3_cv3_unit_squared_targeted.py --workers 6 --cap 13
```

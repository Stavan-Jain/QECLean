# T3-C — Larger G_2 structure

Date: 2026-05-26. HANDOFF_TIER3_CV3 §4 T3-C.

## Result: **FALSIFIED** on Z_12 × Z_12 with gross-style polynomials

The decisive counterexample, **C1**, falsifies the C-v3.1 refined
hypothesis (with odd-weight added) cleanly:

| | C1 violator | (for comparison) bb_288 |
|---|---|---|
| G | Z_12 × Z_12 | Z_12 × Z_12 (SAME) |
| A | x³ + y + y² | x³ + y² + y⁷ |
| B | y³ + x + x² | y³ + x + x² (SAME) |
| weight(A) | 3 (odd ✓) | 3 (odd ✓) |
| weight(B) | 3 (odd ✓) | 3 (odd ✓) |
| G_odd | Z_3 × Z_3 (elem-ab ✓) | SAME |
| c | 3 (≥ 3 ✓) | SAME |
| w_1 per orbit | 54 | 54 (IDENTICAL) |
| C-v3 bound | 18 | 18 (IDENTICAL) |
| d_X | **12** (from SAT) | **18** (published) |
| verdict | **VIOLATION (bound > d)** | tight |

All C-v3.1 hypothesis clauses hold; the bound overshoots d by 6.

## The structural diagnosis

**The same A and B polynomials are tight on Z_12 × Z_6 (= gross)** with
d=12 and bound=12. Moving to Z_12 × Z_12 enlarges the 2-Sylow from
Z_4 × Z_2 to Z_4 × Z_4. The C-v1 invariant w_1 increases (from 36 to
54) but d stays at 12 on this specific (A, B) choice. So C-v1's
scaling with |G_2| doesn't match d's scaling.

## Why C-v1 fails to distinguish C1 from bb_288

The R_O-projections at orbit (1, 1):
- a_O(C1) = `[(3,0)] + ω·[(0,1)] + ω²·[(0,2)]`
- a_O(bb_288) = `[(3,0)] + ω²·[(0,2)] + ω·[(0,3)]`

In y'-basis (y' = b_y - 1 in F_2[Z_4]):
- C1's y-part: `y'(1+y')` — unit factor (1+y') has order 4.
- bb_288's y-part: `y'(1+y'²)` — unit factor (1+y'²) has order 2.

Both elements are R_O-unit-equivalent (multiplying by `(1+y')` is
invertible in R_O). C-v1's w_1 IS designed to be invariant under
R_O-unit multiplication (it measures the min-weight element in the
kernel of mult-by-a_O, and that kernel is determined by the principal
ideal (a_O), which is unit-invariant).

So C-v1 collapses C1 and bb_288 to the same w_1 = 54, but their
BB-code distances differ (12 vs 18).

## Why d differs

The distinguishing factor: in C1, the per_orbit_dual_distance witness
(min weight in fiber-summed (ker M_A)_O = 12) is a TRUE LOGICAL.
In bb_288, the same per_orbit_dual_distance witness is a STABILIZER
(in rowspan of H_X), so d > 12.

Whether the witness is a stabilizer or logical depends on the JOINT
(A, B) structure (specifically, how A's R_O-projection's unit factor
interacts with B's stabilizer rowspan). C-v1 doesn't see this joint
structure.

See [`T3_summary_draft.md`](T3_summary_draft.md) §H_UNIT² investigation
for a candidate refinement based on the unit-factor's algebraic order.

## Other T3-C cases

Per the script (`scripts/tier3_cv3_refined_bcde.py --battery C`):

| label | G | A | B | c | n | k | bound | d | verdict |
|---|---|---|---|---|---|---|---|---|---|
| C1 | Z_12×Z_12 | x³+y+y² | y³+x+x² | 3 | 288 | 16 | 18 | **12** | **VIOLATION** |
| C2 | Z_12×Z_12 | x⁴+y+y² | y⁴+x+x² | 4 | — | 0 | — | — | k=0 |
| C3 | Z_8×Z_6 | 1+y+y² | x+x²+x³ | 6 | — | 0 | — | — | k=0 |
| C4 | Z_8×Z_6 | x+y+y² | x²+xy+x²y | 1 | — | 0 | — | — | out + k=0 |
| C5 | Z_16×Z_6 | x⁴+y+y² | y³+x+x² | 3 | — | 0 | — | — | k=0 |
| C6 | Z_24×Z_6 | x³+y+y² | y³+x+x² | 3 | 288 | — | 18 | — | SAT cap (d≥10) |

## Verdict on T3-C

**FALSIFIED** by C1. The refined C-v3.1 hypothesis is insufficient;
the bound depends on structural information beyond `(elem-ab, c, weight
parity)`. See H_UNIT² investigation as a candidate further refinement.

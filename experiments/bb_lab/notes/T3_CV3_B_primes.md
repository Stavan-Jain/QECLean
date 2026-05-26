# T3-B — Other G_odd primes (Z_5×Z_5, Z_7×Z_7, Z_3×Z_5, Z_3×Z_7)

Date: 2026-05-26. HANDOFF_TIER3_CV3 §4 T3-B.

## Setup

Test the C-v3.1 refined hypothesis (`elem-ab G_odd ∧ c ≥ 3 ∧ both
weights odd`) on groups whose G_odd has primes other than 3. The
suspicion (HANDOFF §8): the factor-of-c pattern might be p=3 specific.

Approach: hand-constructed (A, B) pairs (canonical enumeration on
Z_5×Z_5 is the HANDOFF.md §5 slow path — skipped per user guidance).

Reproduce via:

    uv run python scripts/tier3_cv3_refined_bcde.py --battery B --workers 4

## Cases tested

| label | G | A | B | wA | wB | c | elem-ab | in_domain | n | k | bound | d | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| B1 | Z_5×Z_5 | 1+x+x² | 1+y+y² | 3 | 3 | 5 | ✓ | ✓ | 50 | 0 | — | — | k=0 |
| B2 | Z_5×Z_5 | 1+x+x² | 1+y+x·y | 3 | 3 | 1 | ✓ | ✗ | 50 | 0 | — | — | out + k=0 |
| B3 | Z_5×Z_5 | 1+x+x³ | 1+y+y³ | 3 | 3 | 5 | ✓ | ✓ | 50 | 0 | — | — | k=0 |
| B4 | Z_7×Z_7 | 1+x+x² | 1+y+y² | 3 | 3 | 7 | ✓ | ✓ | 98 | 0 | — | — | k=0 |
| B5 | Z_7×Z_7 | 1+x+x³ | 1+y+y³ | 3 | 3 | 7 | ✓ | ✓ | 98 | 18 | 4 | 4 | **tight** |
| B6 | Z_3×Z_5 | 1+x+x² | 1+y+y² | 3 | 3 | 3 | ✓ | ✓ | 30 | 0 | — | — | k=0 |
| B7 | Z_3×Z_7 | 1+x+x² | 1+y+y² | 3 | 3 | 3 | ✓ | ✓ | 42 | 0 | — | — | k=0 |

## Outcome

1 in-domain testable case (k > 0), tight, **0 violations**.

The "x-only A, y-only B" pattern on these groups gives codes with k=0
(no logicals; distance undefined). This is consistent with the
"4-factor curse" analog: structurally, when A and B are concentrated
on orthogonal axes of an elementary-abelian group, they jointly
annihilate too much / not enough.

The single testable case (B5: Z_7×Z_7 with x+x³, y+y³ polys) was
tight at d = bound = 4.

## Verdict on T3-B

**Insufficient testable evidence** to definitively confirm or
falsify C-v3.1 on non-p=3 G_odd. The conjecture is consistent with
the 1 testable case. A more thorough study would require either:
- Different (A, B) constructions on Z_5×Z_5 / Z_7×Z_7 that produce k > 0
  with c ≥ 3.
- Larger groups (e.g., Z_5 × Z_10 with G_2 = Z_2) where the 4-factor
  curse breaks down.

Neither is in this session's scope. T3-B is **inconclusive**.

## What we DID NOT test

- Pairs (A, B) that have k > 0 on Z_5×Z_5 / Z_7×Z_7 (would require
  non-trivial enumeration or theory work).
- Larger groups with mixed primes (e.g., Z_5 × Z_15 = Z_3 × Z_5²).

# T3-A — weight-4 BB codes over Z_6 × Z_6

Date: 2026-05-26. HANDOFF_TIER3_CV3 §4 T3-A.

## Setup

`G = Z_6 × Z_6` (gross's G_odd structure = Z_3 × Z_3, |G_2| = 4),
weight = 4 polynomials A and B. Filter to **in-scope** (c ≥ 3,
elem-ab G_odd ✓ trivially since G_odd doesn't depend on weight).

Reproduce via:

    uv run python scripts/tier3_cv3_a_weight4.py --limit N --weight 4

## Result: FALSIFIED on weight-4

| metric | value |
|---|:---:|
| Canonical weight-4 pairs enumerated | 8 683 |
| Time to enumerate 8 683 pairs | 268.8s |
| In-scope subset (c ≥ 3) reached | 500 |
| **Violations** | **78 (15.6%)** |
| Tight | 387 (77.4%) |
| Loose | 35 (7.0%) |

## Violator structure

All 78 violations concentrate on **two A-polynomials**:

| A polynomial | violations | structural notes |
|---|:---:|---|
| `1 + y + y² + x` | 65 | non-degenerate (⟨supp⟩ = G); contains "1+y+y²" cube-root vanishing factor |
| `1 + y + y² + y⁴` | 13 | y-only (⟨supp⟩ = {0}×Z_6, index 6 in G); also contains "1+y+y²" factor |

Both A's contain the **cube-root vanishing sub-polynomial `1 + y + y²`**.
This makes A vanish on every Frobenius orbit where the y-character is
a non-trivial cube root.

The C-v3 `w_1(A, O)` values implied (back-solving from bound and c=3):

- `bound = 6 → w_1 = 18`
- `bound = 4 → w_1 = 12`
- `bound = 3 → w_1 = 9`

Yet `d = 2` or `d = 4` for these instances. So `w_1` overestimates
the actual distance by a factor of 1.5–3× even after dividing by c.

## Sample violators

| A | B | c | bound | d | gap |
|---|---|:---:|:---:|:---:|:---:|
| 1+y+y²+y⁴ | 1+y³+x+x·y³ | 3 | 4 | 2 | -2 |
| 1+y+y²+y⁴ | 1+y³+x²+x²·y³ | 3 | 3 | 2 | -1 |
| 1+y+y²+y⁴ | 1+y³+x³+x³·y³ | 3 | 4 | 2 | -2 |
| 1+y+y²+x | 1+x+x³·y³+x⁴ | 3 | 6 | 4 | -2 |
| 1+y+y²+x | 1+x+x³·y³+x⁴·y³ | 3 | 6 | 2 | -4 |
| 1+y+y²+x | 1+x·y+x·y⁴+x³ | 3 | 6 | 4 | -2 |
| 1+y+y²+x | 1+x·y+x³+x⁴·y | 3 | 6 | 2 | -4 |

The worst gap is **-4** (bound exceeds d by 4): e.g.
`A = 1+y+y²+x, B = 1+x+x³y³+x⁴·y³`, where C-v3 predicts `d ≥ 6`
but `d_actual = 2`.

## Why this falsifies

The conjecture statement (C-v3):

> If `G_odd` is elementary abelian AND `c ≥ 3`, then
> `d_X ≥ (1/c) · min_O min(w_1(A,O), w_1(B,O))`.

bb_72_12_6, gross, and bb_288 all have **weight-3 A and B**. The
corpus also has only weight-3 BB pairs (the standard enumeration
target). Weight-4 is out-of-corpus territory.

Within the C-v3 hypothesis (loose elem-ab + c ≥ 3), weight-4 over
Z_6 × Z_6 produces 15.6% violation rate. This is a clean
falsification.

## Possible refinement

The natural narrowing of the hypothesis:

> If `G_odd` is elementary abelian AND `c ≥ 3` AND **`weight(A) = weight(B) = 3`**, then …

This would exclude the T3-A violators by hypothesis. The Bravyi
table's 4 in-scope codes (bb_72, bb_90, gross, bb_288) are all
weight-3, so they still satisfy.

However, the narrowing is unprincipled — there's no obvious algebraic
reason `weight = 3` should be load-bearing. It just happens to be
where the corpus and Bravyi codes live. The narrowed hypothesis
would cover **fewer than 80** corpus rows (= the C-v3 c ≥ 3 subset
minus any weight ≠ 3 entries; the corpus is weight-3 throughout, so
maybe still 74) plus 4 Bravyi codes.

A more principled refinement might be:

- `A` and `B` each have at most one "vanishing-direction" factor
  (the `1 + y + y²` sub-polynomial structure that makes A vanish on
  3 of 4 size-2 orbits simultaneously).
- Or: the orbit-vanishing pattern of A and B is "non-stacked" in a
  specific sense.

Both are speculative; the T3-A data doesn't immediately suggest a
clean structural condition.

## Recommendation

Per HANDOFF_TIER3_CV3 §6, this is the **falsified verdict** for the
C-v3 conjecture as stated. Whether to add a "weight = 3" clause and
declare a narrower theorem, or to shelve the bound entirely, is a
C-v3-round-2 decision.

Skipping or condensing T3-B/C/D/E is reasonable now that T3-A has
falsified — the verdict is clear. But running T3-B (other primes)
briefly confirms the bound's domain isn't even narrower than
"weight = 3 over Z_3 × Z_3 G_odd".

## Sanity check: weight-3 over Z_6 × Z_6 still survives

Running the same script with `--weight 3 --limit 100` on Z_6 × Z_6
should reproduce the C-v3 corpus survival (no violations) — see
end of file (updated when sanity check completes).

# Narrowed hypothesis: elementary-abelian G_odd AND c ≥ 3

## Statement

For a BB code `BB(G, A, B)`:

> **If**
>
> - `G_odd` is loosely elementary abelian (`is_g_odd_elementary_abelian(G)`
>   is True: for every prime `p | |G_odd|`, the p-primary subgroup of
>   G_odd is `(Z_p)^{k_p}`),
> - **AND** `c = [G_a : G_a ∩ G_b] ≥ 3`,
>
> **then**
>
> `d_X(BB(G, A, B)) ≥ ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉`
>
> where `w_1` is the C-v1 invariant and `min_O` is over Frobenius
> orbits where both A and B vanish.

## Where this came from

HANDOFF_C3 §2 narrowed the C-v2 conjecture to require elementary-
abelian G_odd, motivated by:

- bb_108_8_10 was the only Bravyi instance falsifying C-v2.
- bb_108's G_odd = Z_9 × Z_3 has a Z_9 factor (cyclic prime-power).
- The other 4 Bravyi codes have elementary-abelian G_odd.

The C-v3 corpus sweep (this round) found that all 3 894 labeled
corpus rows have elem-ab G_odd in the loose sense, so the elem-ab
condition alone doesn't filter. Adding **c ≥ 3** (per HANDOFF_C3 §6
risk) gives the clean survival condition.

## Why both conditions are needed

| condition | covers gross | excludes bb_108 | corpus violations |
|---|:---:|:---:|:---:|
| elem-ab G_odd alone | ✓ | ✓ | 3 319 (same as C-v2) |
| c ≥ 3 alone | ✓ | ✗ (bb_108 has c=3) | 0 (in corpus) |
| **elem-ab ∧ c ≥ 3** | ✓ | ✓ | **0** |

- "elem-ab alone" excludes bb_108 from hypothesis but doesn't filter
  the corpus c=1, c=2 violations.
- "c ≥ 3 alone" filters the corpus but doesn't exclude bb_108
  externally.
- BOTH together: covers all 4 elem-ab Bravyi codes (tight), excludes
  bb_108 (hypothesis), and produces 0 corpus violations.

## What about narrower / wider versions?

- **Strict single-prime elem-ab**: tightens to G_odd = (Z_p)^k for
  one prime. Excludes bb_90 (G_odd = Z_3 × Z_3 × Z_5). Loses
  coverage of an actual Bravyi instance, so worse.
- **Loose elem-ab + c ≥ 2** (relax c condition): re-introduces 171
  corpus violations (at c=2). Worse.
- **Loose elem-ab + c = 3 exactly**: cleaner cutoff but excludes
  the c=4,5,6 corpus rows (~13 rows, all non-violating). No benefit.

The loose elem-ab ∧ c ≥ 3 form is the **maximal-coverage** version
that survives the corpus.

## Domain size

- Corpus labeled rows in domain: 74 / 3 894 (1.9%).
- Bravyi codes in domain: 4 / 5 (80%).

The domain is **small fraction of BB codes** but **large fraction of
the engineering-target Bravyi family**. This is the structural
distinction made explicit: engineered BB codes live in a
combinatorially special regime where the bound holds.

## Falsification target

A single corpus or Bravyi-table violation falsifies. HANDOFF_C3
verdict options:

- **survives-tight-on-gross-and-clean** ← matched here
- survives-tight-on-gross-but-with-residuals
- survives-but-loose-on-gross
- falsified-on-restricted-domain

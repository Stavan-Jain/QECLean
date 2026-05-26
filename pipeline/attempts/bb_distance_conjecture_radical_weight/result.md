# Result — Tier-2 verdict on the radical-weight distance conjecture (C-v2)

**Verdict: FALSIFIED.**

The conjecture

```
d_X(BB(G, A, B))  ≥  ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉
```

is falsified on multiple grounds. Headline numbers:

- **Corpus sweep**: 3 319 / 3 894 rows violate (85.2%). Pattern is
  concentrated at small `c`: at c = 1, 97% violation rate; at c = 2,
  30%. Zero violations at c ≥ 3 (but only 74 labeled corpus rows).
- **Bravyi-table check**: 4 of 5 Bravyi instances tight, but
  bb_108_8_10 violates: bound = 12 > d_published = 10.
- **All five §5 alternatives also falsified**: any-orbit identical
  to primary, multi-mu slightly tighter but still violates broadly,
  sum violates gross itself, geometric violates 93% of corpus.

The gross-style tightness (4/5 Bravyi + 32 c=3 corpus rows) is a
**coincidence of the elementary-abelian G_odd structure**, not a
structural theorem.

## What the conjecture got right

In the limited subset where:

- `c ≥ 3` (gross-style joint support index),
- AND `G_odd` is elementary abelian (`Z_p × Z_p` for prime p),
- AND polynomial supports are "orthogonally placed",

the conjecture appears to hold and is often tight. This is a real
empirical pattern documented in
[`notes/Cv2_tightness.md`](../../experiments/bb_lab/notes/Cv2_tightness.md):

- bb_72_12_6 (G_odd = Z_3 × Z_3): tight at d=6.
- gross [[144,12,12]] (G_odd = Z_3 × Z_3): tight at d=12.
- bb_288_12_18 (G_odd = Z_3 × Z_3): tight at d=18.

But the conjecture is **not gated** by these conditions in its stated
form. As stated for arbitrary BB codes, it fails.

## What the conjecture got wrong

### Reason 1: bb_108_8_10 (G_odd = Z_9 × Z_3, c = 3)

bb_108_8_10's G_odd is cyclic-prime-power (Z_9) × Z_3, not elementary
abelian. The conjecture computes w_1 = 36 per vanishing orbit (same
shape as gross), c = 3, bound = 12. But d_published = 10.

The conjecture overcounts by 2. The C-v1 numerator `w_1` is
sensitive to per-orbit Galois structure (`|O|` and the field
F_{2^|O|}'s embedding into F_2[G_odd]) in a way that the LP-style
denominator `c` does not correct for. When G_odd is non-elementary,
the orbit-O isotypic component has size that the LP correction
doesn't track.

### Reason 2: The c = 1 (non-degenerate) majority

3 245 of 3 894 corpus rows are non-degenerate (`c = 1`). For these,
the conjecture's RHS is just `min_O min(w_1(A,O), w_1(B,O))`, which
is the proper per-orbit isotypic kernel min weight without any
LP-style shrinkage. This quantity is typically much larger than the
actual code distance (which can be 2 for highly-symmetric A and B),
so the bound dramatically overestimates.

In particular, when A = B, the conjecture predicts `d ≥ w_1`, but
the actual code is degenerate (k = 2 dim ker M_A, often with
weight-1 or weight-2 logicals). 97% violation rate at c = 1.

### Reason 3: All alternatives fail too

The §5 alternatives — any-orbit, multi-mu, sum, geometric — produce
qualitatively similar pictures:
- "sum" violates gross itself (24 > 12) and the corpus, dead immediately.
- "geometric" gives bounds slightly above primary on average,
  produces 3 614 violations.
- "multi-mu" is slightly less violating (3 133) but still falsifies
  bb_108.

No simple variant of the conjecture's structure survives both gross
and bb_108.

## Survivors (substantive follow-up ideas)

A future C-v2 round (or C-v2-narrow) could test:

- **Gate by `G_odd = Z_3 × Z_3` exactly**, with full corpus sweep.
  Z_3 × Z_3 G_odd corresponds to corpus groups Z_6×Z_6 (812 rows)
  and Z_4×Z_6 (106 rows). bb_72, gross, bb_288 all live here.
  bb_108 (Z_9 × Z_3) is excluded.
- **Gate by `c ≥ 3` AND `G_odd elementary abelian`**: 0 violations on
  the c=3 corpus subset implies this gating would have 0 violations
  on the corpus, but it excludes bb_108 and many Bravyi-style
  codes. A weaker conjecture, easier to prove.
- **A "corrected" denominator** that's per-orbit rather than global:
  some quantity `c_O` such that `d ≥ min_O (w_1(A,O) / c_O)`. The
  obstruction is that no simple `c_O` makes bb_72, gross, and bb_108
  all tight simultaneously. This would require new theory.

The C-v2 conjecture is structurally close-but-not-right. The
remaining work is to find what additional refinement closes the
gap. Per HANDOFF_C2 §C-v2.6 stop conditions, this is
**falsified-by-corpus + falsified-by-Bravyi-table** with documented
survival domain and follow-up ideas. The C-v3 (formal proof) step
is **not** taken.

## Per the program's "failures are first-class" principle

This conjecture's falsification is a real contribution to the
broader BB-distance-bound program:

1. It establishes that the gross "factor of 3" is NOT a general
   structural property of BB codes — it's a coincidence of the
   elementary-abelian-G_odd Bravyi family.
2. It identifies a candidate **narrower** conjecture (gated by
   G_odd = Z_3 × Z_3 specifically) that could be pursued in a
   follow-up. The C-v1 substrate (`w_1`) computed during this round
   is reusable for that work.
3. It documents the per_orbit_dual_distance / w_1 divergence
   (HANDOFF_C2 §6 side-quest) — the existing function uses
   fiber-summed constraints, not per-fiber, and is NOT a
   `w_1 / c` shortcut. Future work should treat them as distinct
   quantities.
4. It corroborates Jitman-Ling 2013 (HANDOFF.md §6j): any closed
   bound on non-semisimple BB codes that's tight on gross-style
   instances must reach beyond the per-orbit semisimple-projection
   shape this conjecture (and LP Statement 12) used.

## Recommendation for the broader pipeline

- This artifact stays open with status "falsified" and the
  follow-up ideas in `state.yaml:next_steps`.
- HANDOFF.md should grow a `§6l` entry documenting the
  "radical-weight + LP-style denominator is structurally blind to
  cyclic-prime-power G_odd" pattern. Not modified here per
  HANDOFF_C2 §7's constraint; left for the next handoff.
- The C-v1 module (`radical_weight.py`) remains a clean
  contribution. The bb_radical_bound additions are isolated to the
  C-v2 conjecture and can be removed if undesired (alternative:
  keep as a documented falsification artifact alongside
  `jacobson_radical_bound`).

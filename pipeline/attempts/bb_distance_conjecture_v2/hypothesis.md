# Hypothesis — Tier-2 Round 2 candidate bounds

Round 2 follows Round 1's falsification. The new ground rule (from
HANDOFF.md §6h): every candidate distance lower bound `d ≥ b(G, A, B)`
must have a right-hand side `b` that is a **weight invariant** — a
quantity defined via the minimum non-zero Hamming weight of some
linear subspace, NOT a dimension count.

This round proposes 7 candidates (5 new, 2 reused) and tests them
against the corpus + Bravyi-table reference instances.

## Candidate 1: r2_TZ_lower_recomputed (literature baseline)

**Formula:** `d_X ≥ ⌈min(d_A^⊥, d_B^⊥) / c⌉` with `c = |G_a ∩ G_b|`.

**Weight-invariance check:** numerator `min(d_A^⊥, d_B^⊥)` is a min
over two classical-cyclic-code minimum distances — clearly a weight
invariant. Denominator `c` is structural. Output is a weight invariant.

**Citation:** Lin-Pryadko 2023 arXiv:2306.16400 Statement 12 §IV.F;
equivalent to Kovalev-Pryadko 2013 Theorem 5. **NOT NEW** — included
as a baseline.

**Expected:** survives corpus and Bravyi sweeps (published bound);
loose on gross (TZ is provably loose for c > 1 per LP23 explicit
analysis).

## Candidate 2: r2_tanner_girth_lower

**Formula:** `d ≥ ⌈(tanner_girth + 2) / 4⌉`.

**Weight-invariance check:** tanner_girth is the length of the
shortest cycle in the bipartite Tanner graph — a combinatorial
weight-style invariant (cycle length = weight of cycle support).
Output is a weight invariant.

**Citation:** Sipser-Spielman 1996; specifically the "expansion
implies distance" theorem family. The exact constant depends on
the expansion ratio of the Tanner graph; we use the conservative
`(g+2)/4` form. **NOT NEW.**

**Expected:** survives all sweeps; loose on engineered BB codes
(BB codes typically have girth 6-10 while d can be 6-18+).

## Candidate 3: r2_bch_per_axis_lower

**Formula:** `d ≥ ⌈BCH(A) / c⌉` where `BCH(A)` is the BCH/Hartmann-
Tzeng designed-distance bound for the polynomial's per-axis cyclic
projection. **Restricted to rank-1 (univariate) groups** because
the bivariate-per-axis version is incorrect for sparse polynomials
(see `bch_per_orbit_lower_bound` docstring caveat).

**Weight-invariance check:** BCH(A) depends on the cyclotomic-coset
structure of the support — a weight invariant of the dual code.

**Citation:** Bose-Chaudhuri-Hocquenghem 1960 (canonical BCH bound).
Per-axis projection bound is textbook for product cyclic codes.
**NOT NEW.**

**Expected:** essentially trivial (returns 1) for multivariate;
survives sweeps; loose everywhere.

## Candidate 4: r2_tz_or_girth_composite (NEW packaging)

**Formula:** `d ≥ max(TZ_lower, ⌈(girth+2)/4⌉)`.

**Weight-invariance check:** max of two weight invariants is a
weight invariant. Output bound is a weight invariant.

**Citation:** composition of LP23 Stmt 12 + Sipser-Spielman.
**Composite of two known lower bounds; not a new mathematical
result, but new as a packaged candidate**.

**Expected:** survives sweeps; matches TZ_lower on c=1 cases,
matches girth on c > 1 cases. Should be the strongest non-trivial
survivor.

## Candidate 5: r2_tz_joint_per_orbit_lower (NEW, expected to fail)

**Formula:** `d ≥ ⌈min_{O ∈ V_A ∩ V_B} d_O^⊥_joint(A, B) / c⌉` where
`d_O^⊥_joint` is the joint per-orbit dual distance (min Hamming
weight of vectors in `ker(M_A) ∩ ker(M_B)` confined to orbit O's
isotypical component).

**Weight-invariance check:** numerator is a min over weight
invariants (per-orbit minimum weights); denominator is structural.
Output is a weight invariant.

**Citation:** **NEW-TO-US.** Refinement of LP23 Stmt 12 using joint
per-orbit kernel min weights instead of global d_A^⊥, d_B^⊥.

**Rationale:** joint per-orbit min weight is provably ≥ global
min_wt_ker, so the numerator is bigger and the resulting bound is
potentially tighter than TZ_lower. **However**, this also means the
bound might EXCEED `d_X` (which is upper-bounded by global d_A^⊥),
and thus VIOLATE. Corpus test will determine.

**Expected:** likely falsified due to numerator overcounting.

## Candidate 6: r2_tz_safe_lower

**Formula:** `d ≥ min(TZ_lower, d_A^⊥, d_B^⊥)`.

**Weight-invariance check:** min of weight invariants is a weight
invariant.

**Citation:** safety cap; vacuous in practice since TZ_lower ≤ d_A^⊥
when c ≥ 1.

**Expected:** identical to TZ_lower.

## Candidate 7: r2_support_indicator_lower (NEW, expected to fail)

**Formula:** `d ≥ ⌈min_wt_ker_A / |V_A ∩ V_B|⌉` where `|V_A ∩ V_B|`
is the count of orbits where both A and B vanish on G_odd.

**Weight-invariance check:** numerator is weight invariant (classical
dual distance); denominator is a structural count. Output is a
weight invariant.

**Citation:** **NEW-TO-US.** Heuristic replacement of TZ's
`c = |G_a ∩ G_b|` with a different structural denominator.

**Rationale:** each joint vanishing orbit is a potential source of
logical operator support; the ratio `d_A^⊥ / |V_A ∩ V_B|`
approximates "each orbit contributes at least 1/|V_A ∩ V_B| of the
dual code's minimum weight" — but this is heuristic, not derived.

**Expected:** falsified by a wide margin (the denominator is
typically much smaller than `c`, inflating the bound).

## Methodology

For each candidate:
1. Compute the bound on every corpus row (3894 rows with `d_exact`).
2. Compute the bound on each Bravyi-table reference instance.
3. Classify each row as:
   - **tight** if bound == d_exact
   - **loose** if bound < d_exact
   - **VIOLATION** if bound > d_exact (falsifies candidate)

A single violation falsifies a candidate. Survivors are ranked by
tightness rate.

## Bravyi-table gross tightness check

The headline benchmark: gross `[[144, 12, 12]]`. The previous
literature analysis (LP23 Stmt 12 with `c = 8`) gives bound = 2.
Any candidate that surpasses this on gross is interesting; any
candidate that matches it is a known bound.

**No candidate in this round is expected to surpass bound=2 on
gross.** The structural reason: every candidate uses denominators
on the same order as `c = 8`, and the numerators are no larger than
`min_wt_ker_A = 12`. The largest possible ratio is `12 / 1 = 12`
(which would require `c = 1`, not gross's `c = 8`).

The closing-of-the-gap question remains open. Round 2 is **not
expected to solve it**; the goal is to lay down a corpus of
well-formed (weight-invariant) candidates and demonstrate the new
methodology.

# Result — Tier-2 Round 2 verdict on weight-invariant candidate bounds

## Per-candidate verdict

| Candidate | Verdict |
|---|---|
| r2_TZ_lower_recomputed | survives-but-loose-on-gross (literature baseline) |
| r2_tanner_girth_lower | survives-but-loose-on-gross |
| r2_bch_per_axis_lower | survives-trivially (returns 1 for multivariate) |
| r2_tz_or_girth_composite | survives-but-loose-on-gross (**RECOMMENDED**) |
| r2_tz_joint_per_orbit_lower | **falsified** (115 corpus violations) |
| r2_tz_safe_lower | survives-but-loose-on-gross (identical to TZ_lower) |
| r2_support_indicator_lower | **falsified** (3068 corpus violations) |

No candidate in this round is **tight on gross**. All survivors give
bound ≤ 2 vs gross's actual d = 12. This is consistent with the open
question in Lin-Pryadko 2306.16400 §IV.F (closing the gap between
`⌈d/c⌉` and `d_A^⊥` for `c > 1`) — Round 2 does not solve it.

## Detailed verdicts

### `r2_TZ_lower_recomputed` — survives, baseline

**Verdict:** survives-but-loose-on-gross.

- Corpus: 0 violations on 3836 applicable rows; 4 tight (0.1%).
- Bravyi: bound = 2 on bb_72_12_6 (d=6), bb_90_8_10 (d=10),
  bb_108_8_10 (d=10), gross (d=12). bb_288_12_18: skipped.
- This is the Lin-Pryadko Statement 12 lower bound. **Already in
  the literature.** Included as a sanity-check baseline that the
  evaluation pipeline is correctly classifying.

### `r2_tanner_girth_lower` — survives, 11.7% tight

**Verdict:** survives-but-loose-on-gross.

- Corpus: 0 violations on 3894 rows; 457 tight (11.7%). Strongest
  per-group tightness on Z3xZ3 (75%) and Z3xZ4 (43.8%).
- Bravyi: bound = 2 everywhere.
- The Sipser-Spielman expander-style bound `(g + 2) / 4` is
  textbook; **NOT NEW** for qLDPC. The high tightness rate on
  small-distance BB codes (`d_exact = 2`) is essentially trivial
  (the bound floors at 1, so it's tight when `d = 2`).

### `r2_bch_per_axis_lower` — survives, trivial

**Verdict:** survives-trivially (no violations because the bound
returns 1 in almost all cases).

- The BCH per-axis-then-MAX construction is **mathematically
  incorrect** for sparse polynomials (e.g. `A = 1 + x + x^2` over
  `Z_3 × Z_6` has no y-dependence; BCH would claim `d_B^⊥ ≥ 6`
  based on the y-axis having all 5 consecutive zeros in the
  complement, but actually `d_A^⊥ = 2`). The implementation
  restricts to univariate cyclic groups (`G.rank == 1`); for
  multivariate it returns the trivial lower bound 1.
- After restriction: 0 violations on 3894 rows, 0 tight.
  Essentially a vacuous lower bound on BB codes.
- **Worth keeping as a feature** for future multivariate
  refinements (Hartmann-Tzeng, Roos) but not as a candidate bound
  itself.

### `r2_tz_or_girth_composite` — survives, 11.9% tight (RECOMMENDED)

**Verdict:** survives-but-loose-on-gross.

- Corpus: 0 violations on 3836 rows; 458 tight (11.9%) — **best
  among survivors**.
- Bravyi: bound = 2 on all instances; skipped on bb_288 (column
  unavailable).
- **Not new mathematics**: `max` of two known lower bounds. But
  the composite is the strongest engineering candidate available
  from the surveyed lower bounds.

### `r2_tz_joint_per_orbit_lower` — FALSIFIED

**Verdict:** falsified (115 corpus violations, 2.95%).

**Mechanism**: the per-orbit constraint EXCLUDES cross-orbit
cancellation in the kernel, inflating the numerator above the
global `d_A^⊥`. This makes the bound exceed the textbook upper
bound `d_X ≤ d_A^⊥` in some cases.

**Smallest violation:**

```
Row 5632c6ff: G = Z_3 × Z_6, A = 1 + y + y², B = 1 + x + x²
d_exact = 2, bound = 8 (violates by +6)
```

**Conclusion**: per-orbit refinement of the TZ numerator is the
wrong direction — the per-orbit kernel min weight is an UPPER
bound on the global kernel min weight, not a lower bound. Using
it as the LB numerator gives an invalid candidate.

### `r2_tz_safe_lower` — survives, identical to TZ

Cap by textbook upper bound. In practice no instance hits the cap
because TZ_lower ≤ d_A^⊥ structurally. Identical behavior to
`r2_TZ_lower_recomputed`.

### `r2_support_indicator_lower` — FALSIFIED

**Verdict:** falsified (3068 corpus violations, 79.7%).

**Mechanism**: the denominator `|V_A ∩ V_B|` (count of joint
vanishing orbits) is typically much smaller than `c = |G_a ∩ G_b|`,
so the bound `d_A^⊥ / |V_A ∩ V_B|` is much larger than
`d_A^⊥ / c`. The candidate has no defensible derivation.

**Smallest violation:**

```
Row 3eaf235b: G = Z_3 × Z_6, A = 1 + y + x, B = 1 + y + x
d_exact = 2, bound = 12 (violates by +10)
```

**Conclusion**: this candidate is cautionary — it directly
violated the rule that the denominator must be defensible.
Included to demonstrate the failure mode.

## Most informative finding

**A general principle for Round 3+**: candidates that REFINE the
TZ numerator (e.g. per-orbit min weight) tend to fail because the
refinement makes the numerator larger, not smaller. The TZ
numerator `min(d_A^⊥, d_B^⊥)` is already an upper bound on the
"useful" weight content; any per-orbit slicing tends to remove
the lowest-weight kernel elements (mixed across orbits), inflating
the minimum and breaking the lower bound.

**The right direction for future refinement**: reduce the TZ
**denominator** `c = |G_a ∩ G_b|` while preserving its structural
meaning. This is hinted at by the Lin-Pryadko §IV.F open question:
the gap `⌈d_A^⊥ / c⌉ ≤ d ≤ d_A^⊥` is closed only at `c = 1`. A
refinement that gives an "effective c" smaller than `|G_a ∩ G_b|`
would tighten the bound on engineered BB codes like gross.

Concrete shape: `d ≥ ⌈d_A^⊥ / c_eff(A, B)⌉` where `c_eff` is a
new structural feature (still in the spirit of LP23) that's
strictly smaller than `c` whenever specific structural conditions
hold. Empirically derivable from corpus tightness analysis.

## Recommended Tier-3 next step

**Do NOT** promote any current survivor to Tier 4 (Lean) as a new
result. The survivors are:
- `r2_tz_or_girth_composite`: composite of literature bounds; could
  be formalized in Lean as a "first Lean formalization of LP Stmt 12
  + Sipser-Spielman composite" but this is documentation work, not
  a new mathematical result.
- TZ_lower itself: textbook.

**Tier 3 should**:
1. Adversarially test `r2_tz_or_girth_composite` on synthetic
   perturbations of gross polynomials (similar to T3 Round 1's
   adversarial sweep).
2. Investigate the Hartmann-Tzeng and Roos bounds for multivariate
   cyclic codes as potential new candidates for Round 3.
3. Investigate `c_eff` denominator refinements as a Round-3
   candidate.

## Open question for Tier 3

**The structural blind spot of all current candidates**: every
candidate that uses the intersection subgroup `c = |G_a ∩ G_b|`
gives bound = 2 on gross. The reason: `|G_a ∩ G_b| = 8` and
`min(d_A^⊥, d_B^⊥) = 12`, so `⌈12/8⌉ = 2`. Closing the gap to
the true `d = 12` requires a 6× tighter denominator (effectively
treating `c` as 1).

The gross polynomials `A = x^3 + y + y^2` and `B = y^3 + x + x^2`
have a specific structural feature: each is "axis-orthogonal" (the
support has 1 monomial purely in x-axis and 2 monomials purely in
y-axis, or vice versa). This forces specific cyclotomic-coset
structure that the per-axis BCH bound CANNOT see but the Hartmann-
Tzeng / Roos multivariate refinement might.

**Specifically**: any candidate that doesn't see the
**axis-orthogonality** of `supp(A)` and `supp(B)` (i.e. the partial
factorization `A = A_x(x) + A_y(y)`, `B = B_x(x) + B_y(y)`) is
doomed to give a loose-on-gross bound. Future Round-3 candidates
must exploit this.

## Citation check

Per HANDOFF.md §6a, every claim of novelty must be cross-checked
against:
- Lin-Pryadko 2306.16400
- Kovalev-Pryadko 2013 (arXiv:1212.6703)
- Bravyi 2024 (arXiv:2308.07915)
- Panteleev-Kalachev (arXiv:2012.04068)
- Wang-Pryadko 2022 (arXiv:2203.17216)
- Raveendran et al. 2025 (arXiv:2503.07567)
- Otjens 2025 (arXiv:2502.17052)

**All surviving candidates** correspond to known literature
bounds (per `experiments/bb_lab/notes/T2.3_literature_survey.md`):
- `r2_TZ_lower_recomputed`: Lin-Pryadko Stmt 12.
- `r2_tanner_girth_lower`: Sipser-Spielman / general LDPC.
- `r2_bch_per_axis_lower`: BCH 1960 (when restricted to univariate).
- `r2_tz_or_girth_composite`: composition.
- `r2_tz_safe_lower`: TZ_lower with no-op cap.

**Falsified candidates** (`tz_joint_per_orbit`, `support_indicator`)
were NEW-TO-US heuristics, not literature bounds. Their
falsification confirms the literature's structural reasoning: these
heuristic refinements are not valid distance lower bounds.

## Implementation status

- `experiments/bb_lab/src/bb_lab/weight_invariants.py`: new module
  with per_orbit_dual_distance, tz_lower_bound (callable),
  bch_per_orbit_lower_bound, joint_kernel_min_weight,
  joint_per_orbit_dual_distance, support/intersection subgroup
  order helpers. 23 unit tests pass.
- `experiments/bb_lab/scripts/tier2_candidates_r2.py`: 7 candidates
  with direction-aware evaluation harness.
- `experiments/bb_lab/scripts/tier2_eval_r2.py`: corpus + Bravyi
  evaluation driver, writes `notes/T2R2.4_evaluation.md`.
- No modifications to forbidden files
  (`features.py`, `canonical.py`, `algebraic_features.py`,
  `enumerate_bb.py`, `cli.py`, `tier2_explore.py`,
  `tier2_candidates_lit.py`, `tier3_*.py`).
- Full test suite: 153 passed, 2 skipped, 3 deselected (up from
  130; 23 new tests).

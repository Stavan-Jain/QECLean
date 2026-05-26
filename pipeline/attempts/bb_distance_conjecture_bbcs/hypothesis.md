# Hypothesis — BBCS 2016 apparent distance lower bound for BB codes (Tier 2 Round 4)

## Setting

A BB code `BB(G, A, B)` has X-distance

    d_X  =  min wt v ∈ ker(H_Z) \ rowspan(H_X)

over `(v_a, v_b) ∈ F_2^{2|G|}`. Round 3 attempted

    d_X(BB(A, B))  ≥  min(d_A^⊥, d_B^⊥)   when single-block dominance S(A, B) holds,

where `d_A^⊥` was lower-bounded by classical multivariate
Hartmann-Tzeng. Round 3 failed because (per HANDOFF §6i and
T2R3.4_eval.md) BB's `G_odd` is non-cyclic and `F_2[G]` is
non-semisimple for the engineering target (gross), and the bound
returned 1 uniformly on all 5 Bravyi codes.

Round 3's recommendation, quoted verbatim:

> *"Bernal-Bueno-Carreño-Simón 2016 apparent distance for full
> multivariate abelian codes (handles non-cyclic G properly via
> hypermatrix manipulation; reduces bivariate from exponential to
> linear complexity)."*

## Conjecture

**Hypothesis H_bbcs**: There exists a structural condition `S(A, B)`
under which the BBCS apparent distance `d^*` (Bernal-Bueno-Carreño-
Simón 2016) of the per-block annihilator code gives a lower bound:

    d_X(BB(A, B))  ≥  min(d^*(ker M_A), d^*(ker M_B))   when S(A, B) holds.

The BBCS algorithm computes `d^*` of a hypermatrix associated with
the generating idempotent of the code, via iterative "involved
hypercolumn" discrepancy sequences. The headline strengths versus
classical HT:

1. **Non-cyclic G**: BBCS's hypermatrix machinery handles
   `G = Z_{r_1} × ... × Z_{r_s}` directly, without needing a
   full-G generator step. Cyclic-G univariate HT is a special
   case (s = 1).

2. **Tightness gap**: BBCS's strong apparent distance (Theorem 22
   plus discrepancy iteration) is **tight** on many cyclic codes
   where classical BCH/HT is loose (Camion 1971's result that
   apparent-distance ≥ all BCH bounds).

3. **Complexity**: Sabin's 1992 exponential algorithm reduced to
   linear in the bivariate case (Remark 20 of BBCS 2016).

## Working version of S(A, B)

To convert to a true lower bound on `d_X(BB(A, B))` we need a
condition that asserts the single-block witness in `ker(M_A^T)` (or
`ker(M_B^T)`) is the minimum-weight X-logical. Candidate forms,
inherited from Round 3:

- **descriptive**: `d_X = min(d_A^⊥, d_B^⊥)` (the textbook upper bound
  is tight). Checkable against `d_exact` on labelled corpus rows
  but not predictive.
- **predictive (BBCS-internal)**: a condition derived from the
  structure of the BBCS witness — e.g. "the BBCS apparent-distance
  witness `χ_β` for A is **not** in the joint defining set of
  `(A, B)` viewed as a `2|G|`-dimensional abelian code."
- **predictive (algebraic)**: `gcd(A, B) = 1` in `F_2[G]` plus a
  support-overlap condition (analogous to Pesah-style coprimality).

Round 4's task was to evaluate Hypothesis H_bbcs on the corpus and
the 5 Bravyi instances, with `bb_apparent_bound(grossA, grossB,
Z_12×Z_6) ≥ 8` as the threshold to beat Round 3, and `≥ 12` as the
threshold to be tight on gross.

## Why Round 4's hypothesis fails before evaluation

The BBCS 2016 paper's preliminaries (Section II) state that the
framework applies only to abelian codes in `F_q[G]` with
`gcd(|G|, q) = 1`, i.e. `F_q[G]` semisimple. Quoting the paper
verbatim:

> *"We deal with abelian codes in the semisimple case; that is, we
> always assume that gcd(r_k, q) = 1 for every k = 1, …, s."*

The assumption is reiterated at the start of Section III (the main
algorithmic section), in Theorem 22 (the minimum-apparent-distance
theorem), and Theorem 25 (the multivariate BCH bound). The 2017
companion paper (Bernal-Guerreiro-Simón, arXiv:1704.03761) states
the same assumption in Section 2, Page 3.

For the BB program: `q = 2` and the Bravyi instances have

| code | G | \|G\| | F_2[G] semisimple? |
|---|---|---:|:---:|
| bb_72_12_6 | Z_6 × Z_6 | 36 | NO (even) |
| bb_90_8_10 | Z_15 × Z_3 | 45 | yes |
| bb_108_8_10 | Z_9 × Z_6 | 54 | NO |
| gross | Z_12 × Z_6 | 72 | **NO** |
| bb_288_12_18 | Z_12 × Z_12 | 144 | NO |

The engineering target (gross) is in the **out-of-scope** regime
for BBCS.

Therefore Hypothesis H_bbcs cannot, as stated, give a lower bound
on `d_X(gross)`. The Round 3 obstruction (non-semisimple F_2[G])
is not lifted by BBCS — BBCS lifts only the orthogonal "G_odd
non-cyclic" obstruction.

This is the **`shelved-paper-doesnt-help`** branch of the T2R4
verdict tree, and the spec explicitly instructs: stop here.

## What would lift the obstruction (out of scope for this round)

The Round 4 hypothesis would have to be **replaced** (not refined)
with a fundamentally different mechanism. Candidates documented in
`state.yaml` next_steps:

1. A weight invariant for the radical of F_2[G] (literature gap; no
   known reference).
2. Cover-graph or chain-map transfer bounds (Pesah et al. 2025) —
   structural, not algebraic.
3. Homological-surgery bounds (Hsieh-Le Gall 2020) — different
   algebraic framework that doesn't require semisimplicity.

None of these can be confused with a "refinement of BBCS"; they are
distinct programs.

## See also

- `experiments/bb_lab/notes/T2R4.0_literature.md` — detailed
  literature triage with quotes and references.
- `pipeline/attempts/bb_distance_conjecture_ht_roos/result.md` —
  Round 3 verdict that motivated this round.
- `experiments/bb_lab/HANDOFF.md` §§6h, 6i — the program-wide
  obstacles that BBCS does not address.

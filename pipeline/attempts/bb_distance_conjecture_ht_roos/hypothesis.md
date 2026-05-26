# Hypothesis — HT/Roos lower bound on BB code distance (single-block-dominance regime)

## Setting

A BB code `BB(G, A, B)` has X-distance

    d_X  =  min wt v ∈ ker(H_Z) \ rowspan(H_X)

over `(v_a, v_b) ∈ F_2^{2|G|}`. Textbook CSS theory gives the
**upper bound** (HANDOFF §6h)

    d_X  ≤  min(d_A^⊥, d_B^⊥)

where `d_A^⊥ = min wt ker(M_A)` is the classical dual distance of
the per-block circulant `M_A`. Equality holds iff the minimum-weight
nontrivial X-logical is a "single-block witness", i.e.

    (f, 0) ∈ ker(H_Z) \ rowspan(H_X)   with   f ∈ ker(M_B^T) = ker(M_{B_rev}).

## Conjecture

**Hypothesis H_ht_roos**: There exists a structural condition `S(A, B)`,
computable from `(G, A, B)`, such that

    S(A, B)  ⟹  d_X(BB(A, B))  =  min(d_A^⊥, d_B^⊥)
              ⟹  d_X(BB(A, B))  ≥  min(mv_ht(nv(A)), mv_ht(nv(B)))

where:
  * `nv(A) ⊆ Ĝ_odd` is the **non-vanishing set** of A: the F̄_2
    characters where `Â(χ) ≠ 0`. This is the textbook defining set
    of the annihilator code `ker M_A`.
  * `mv_ht(·)` is the multivariate Hartmann-Tzeng bound on the
    minimum distance of a cyclic code from its defining set, in the
    sense of Saints-Heegard 1995 (extending Hartmann-Tzeng 1972 +
    Camion 1970 to multivariate abelian codes).

## Working version of S(A, B)

For the corpus evaluation, we use a **descriptive** (rather than
predictive) version of `S(A, B)`:

    S(A, B)  :=  d_X(BB(A, B)) = min(d_A^⊥, d_B^⊥),

verified per-row against the corpus's `d_exact`. This is tautologically
the right condition for the bound chain to give a real lower bound,
but it requires knowing `d_X` (typically a SAT computation). A
**predictive** version of S(A, B) closed in `(G, A, B)` is the
mathematical content of the conjecture, but it lies beyond this round.

## Implementation caveats

The multivariate HT bound has two correctness restrictions:

1. **Semisimple `F_2[G]` only**: HT applies to the cyclic code's
   minimum distance only when `gcd(|G|, char F) = 1`. For `F_2` and
   even `|G|`, `F_2[G]` is non-semisimple — characters of even order
   don't lift to F̄_2, and the F_2-code's min distance can be strictly
   less than HT predicts (due to the Jacobson-radical contribution).
   We implement the bound on the semisimple quotient `F_2[G_odd]`
   and gate even-`|G|` rows out of the bound's validity claim.

2. **Cyclic `G_odd` only (working impl)**: my brute-force
   "longest AP in `nv(A)` along a full-G-generator step" bound is
   provably correct only for *cyclic* G_odd (where a full-G generator
   exists). For non-cyclic G_odd (e.g. Z_3 × Z_3 with gcd(3,3) = 3),
   the genuine multivariate Camion bound exists (Bernal et al. 2016)
   but is more sophisticated than what we implemented; my impl
   returns 1 (trivial) on non-cyclic G_odd.

   This implementation gap explains why all 5 Bravyi codes get
   `bb_ht_bound = 1` (their G_odd is non-cyclic for the 4 even-|G|
   cases, and bb_90's G_odd = Z_15 × Z_3 has gcd(15,3) = 3 ≠ 1).

## Predicted behavior

Per the §6i finding (BB engineering target lives in the degenerate
regime), HT/Roos applied per-block is expected to be **structurally
loose** on Bravyi codes. The condition `S(A, B)` is expected to fail
for Bravyi codes because the dominant X-logical is *mixed-block*
(this is what gives the d ≈ √n scaling Bravyi engineered).

If the conjecture holds in the predicted way (loose on Bravyi,
tight elsewhere), the verdict is `survives-loose-on-gross`.
If somewhere on the corpus the bound exceeds `d_exact` under
satisfied S(A, B), the verdict is `falsified`.

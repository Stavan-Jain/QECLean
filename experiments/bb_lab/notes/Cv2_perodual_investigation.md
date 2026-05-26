# C-v2 side-quest — `per_orbit_dual_distance` vs `w_1`

Date: 2026-05-26. HANDOFF_C2 §6.

## Hypothesis

Per HANDOFF_C2 §6, on non-semisimple G,
`per_orbit_dual_distance(A, O)` might equal `w_1(A, O) / c` for some
orbit-specific `c`. If true, the C-v2 conjecture
`d_X ≥ (1/c) · min_O min(w_1(A,O), w_1(B,O))` would simplify to
`d_X ≥ min_O min(per_orbit_dual_distance(A,O), per_orbit_dual_distance(B,O))`.

## Test setup

Compute the ratio `w_1(A, O) / per_orbit_dual_distance(A, O)` across:

1. Gross's three vanishing orbits (G = Z₁₂ × Z₆).
2. Semisimple Z₃ × Z₅, Z₃ × Z₃ test polynomials.
3. Small non-semisimple corpus rows: Z₃ × Z₄, Z₃ × Z₆, Z₄ × Z₆,
   Z₅ × Z₆, Z₆ × Z₆.

## Results

| group | A | orbit (rep) | \|O\| | μ_O | per_orbit_dual | w_1 | ratio |
|---|---|---|:---:|:---:|:---:|:---:|:---:|
| Z₁₂×Z₆ | x³+y+y² (gross) | (0,1) | 2 | 2 | 12 | 36 | **3** |
| Z₁₂×Z₆ | x³+y+y² (gross) | (1,1) | 2 | 2 | 12 | 36 | **3** |
| Z₁₂×Z₆ | x³+y+y² (gross) | (1,2) | 2 | 2 | 12 | 36 | **3** |
| Z₃×Z₅ | 1+x+x²·y | (1,0) | 2 | 1 | 10 | 10 | 1 |
| Z₃×Z₃ | 1+x·y+x²·y² | (1,1) | 2 | 1 | 6 | 6 | 1 |
| Z₄ | (1+x)² | (0,) | 1 | 2 | 2 | 2 | 1 |
| Z₃×Z₄ | 1+x+x² | (1,0) | 2 | 4 | 2 | 2 | 1 |
| Z₃×Z₆ | 1+y+y² | (0,1) | 2 | 1 | 4 | 12 | **3** |
| Z₃×Z₆ | 1+y+y² | (1,1) | 2 | 1 | 4 | 12 | **3** |
| Z₃×Z₆ | 1+y+y² | (1,2) | 2 | 1 | 4 | 12 | **3** |
| Z₄×Z₆ | 1+y+y² | (0,1) | 2 | 4 | 4 | 4 | 1 |
| Z₅×Z₆ | 1+y+y² | (0,1) | 2 | 1 | 4 | 20 | **5** |
| Z₅×Z₆ | 1+y+y² | (1,1) | 4 | 1 | 4 | 16 | **4** |
| Z₅×Z₆ | 1+y+y² | (1,2) | 4 | 1 | 4 | 16 | **4** |
| Z₆×Z₆ | 1+y+y² | (0,1) | 2 | 2 | 4 | 12 | **3** |
| Z₆×Z₆ | 1+y+y² | (1,1) | 2 | 2 | 4 | 12 | **3** |

## Interpretation

The ratio `w_1 / per_orbit_dual_distance`:

1. **Is NOT a global function of the LP `c`** (or even of the
   support-subgroup index `sgi_A`).
   - Gross has `sgi_A = 3` AND ratio = 3.
   - Z₃ × Z₄ has `sgi_A = 4` BUT ratio = 1.
   - Z₅ × Z₆ has `sgi_A = 5` AND ratio = 5 for one orbit, 4 for
     others.
2. **Equals 1 exactly when**:
   - G_2 trivial (semisimple G), OR
   - G_odd trivial (chain ring like Z_4), OR
   - The orbit O includes generators of G_odd that are coprime to
     the support's "missing axis" (in some empirical sense).
3. **Is greater than 1 when both G_odd and G_2 are non-trivial AND
   A's support doesn't generate the relevant orbit's axis-extension**.
   - Z₃ × Z₆ A = 1+y+y²: A is y-only; ratio = 3 for all vanishing
     orbits.
   - Z₅ × Z₆ A = 1+y+y²: A is y-only; ratio = 5 for the y-only
     orbit, 4 for the x×y orbits.

Concretely, the ratio appears to depend on **per-orbit Galois data
plus the support's interaction with that orbit's "missing axis"** —
which is more refined than any single integer `c`.

## Conclusion

**Hypothesis (a) (`per_orbit_dual = w_1 / c`) is FALSE in general.**
The two quantities differ by orbit-and-polynomial-dependent factors
that don't collapse to a single integer.

**Hypothesis (b)** (`per_orbit_dual_distance` is "fiber-summed and
this is a genuine subtlety, not a simple division by c"): supported.
The function computes a meaningful but distinct quantity.

**Implication for C-v2**: substituting `per_orbit_dual_distance` for
`w_1` in the conjecture does not save it. Quick check on the failing
case Z₃ × Z₆ A=B=1+y+y² (d=2):
- `min_O per_orbit_dual_distance(A, O) = 4`. Conjecture says `d ≥ 4`,
  but `d_actual = 2`. **Still violates.**

So even the "use podd instead" workaround doesn't survive.

## Should `per_orbit_dual_distance` be fixed?

The question becomes: is the existing function's fiber-summed
constraint **incorrect**, or is it a **legitimate alternative
quantity**?

Argument for "incorrect":
- The function's docstring claims it computes the "min Hamming weight
  in the orbit-O isotypic component of ker(M_A)". For semisimple G,
  this is exact. For non-semisimple G, the constraint is weaker, so
  the F_2-subspace is *larger* than the true O-isotypic kernel, and
  the min weight is *less than or equal to* the true value.
- So the function returns a **lower bound** on the true per-orbit
  dual distance, not the true value.

Argument for "legitimate alternative":
- The fiber-summed quantity itself is well-defined and might have
  uses in other Tier 2 work where fiber-summing has algebraic
  meaning.

**Recommendation**: do NOT modify `per_orbit_dual_distance` as part
of C-v2. The fix would change a public API and is not load-bearing
for the C-v2 verdict (which is "falsified"). Document the divergence
and the fact that the existing function returns a lower bound rather
than the proper per-orbit dual distance, but leave the function
alone. A separate refactor can address it after Tier-2/3 conjectures
that depend on it are surveyed.

The C-v1 module's `w_1` is the correct quantity for the proper
per-orbit isotypic kernel min weight on non-semisimple G; downstream
work should reach for `w_1` when that's what's needed.

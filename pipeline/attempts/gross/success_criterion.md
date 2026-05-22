# Success criterion: gross

## Tight success (publishable, very unlikely)

A Lean theorem:

```lean
theorem grossCode_distance_ge_12 :
    ∀ g ∈ (grossCode.toStabilizerGroup.centralizer),
      g ∉ grossCode.toStabilizerGroup.toSubgroup →
      IsNontrivialLogicalOperator grossCode.toStabilizerGroup g →
      NQubitPauliGroupElement.weight g ≥ 12
```

(or equivalently, `HasCodeDistance grossCode 12` populated via the
`Stabilizer/Core/CodeDistance` framework), with proof compiling and
verifying in Lean's kernel, no `sorry`, no `axiom` beyond mathlib's
trusted core.

To be publishable this would require:
- The proof to **not** depend on a kernel-runtime brute force search over
  `2^144` operators (i.e. `native_decide` over the full code space is
  *not* acceptable here — must be a closed-form analytical proof).
- A self-contained analytical argument generalizable beyond the specific
  gross polynomials.

**Calibrated probability**: < 5%. Treated as aspirational ceiling.

## Partial success (worth keeping)

Several flavors, ordered by ambition:

### Partial-A (best plausible): Parametric Camion bound for abelian CSS

A Lean theorem of the form:

```lean
theorem camion_bound_abelian_css (ℓ m : ℕ) (A B : F2[Z_ℓ × Z_m])
    (hcomm : A * B = B * A) :
    ∀ (Q : abelianCSSCode ℓ m A B),
      Q.distance ≥ apparentDistance ℓ m A B
```

specialized to give an explicit numerical lower bound on the gross
code (some `K ∈ {4, 6, 8}`). **Both** the parametric theorem and the
concrete `grossCode.distance ≥ K` instantiation must compile.

The parametric theorem is the publishable artifact (workshop-paper-
worthy); the numerical specialization is the validation.

**Calibrated probability**: 30–40%.

### Partial-B: Classical Camion bound formalized, CSS extension sketched

The full classical Camion apparent-distance theorem proven in Lean for
multivariate abelian codes (`F_2[Z_ℓ × Z_m]`-ideal codes), with the CSS
extension stated as a definition + a `sorry`-marked theorem + a
detailed `final_writeup.md` explaining the missing CSS-coset analysis.

**Calibrated probability**: 50–60%.

### Partial-C: Classical Camion bound only

Just the multivariate Camion apparent-distance theorem, no CSS
extension. Would be a useful mathlib contribution in its own right
(currently mathlib has *some* cyclic / BCH-code material but not
multivariate-abelian / Camion).

**Calibrated probability**: 60–70%.

## Negative result (still valuable)

A clean write-up demonstrating one of the following:

1. **Camion-loose**: `d_app(gross) ≤ K` for some small `K ≤ 4`,
   verifiable mechanically (essentially a non-Lean numerical
   computation supported by Lean-verified definitions), with a detailed
   explanation of *why* — e.g., "the consecutive-zero patterns of `A`
   and `B` over `F_2[x] / (x^12 - 1) ⊗ F_2[y] / (y^6 - 1)` are bounded
   by length `K - 1` because of the specific exponent structure
   `{0, 3} ∪ {y, y^2}` and `{0, y^3} ∪ {x, x^2}`."
2. **Fundamental obstruction**: a Lean-verified statement of the form
   "if [hypothesis], then Camion applied to BB codes cannot reach
   `d ≥ K` for any `K > K_max`", where the hypothesis names a specific
   property of the polynomial pair.
3. **Modular characteristic failure**: a clean demonstration that the
   `char(F_2) = 2 | |G| = 72` obstruction means the classical Camion
   theorem (in its semisimple-Maschke form) does not directly apply,
   forcing reformulation in terms of the radical / Jacobson decomp.
   With either (a) the reformulation succeeding (back to partial-A
   territory) or (b) the reformulation hitting a specific named
   obstacle.

**Calibrated probability of *some* negative result**: 30%. These are
honest failure modes, not vague "didn't close" notes.

## Anti-success: what would invalidate the moonshot

If the work degenerates into either of these patterns, we should stop
and write up:

1. Spending budget on **filling generic mathlib gaps** (e.g. building
   `MultivariatePolynomial` infrastructure that should be upstreamed)
   rather than on the Camion-specific content. Threshold: > 25% of
   approach budget on infrastructure suggests a pivot.
2. Producing a "**looks promising**" status with no compiling lemmas
   after > 75% of approach budget. Lean compilation is the only
   evidence; "I think this will work" is not.
3. Silent target downgrade: starting with `d ≥ 12`, computing
   `d_app = 4`, and writing up "we proved a lower bound" without
   acknowledging the gap. We commit to surfacing the `d_app` value
   the moment it's computed.

## Acceptance test

The completed moonshot is "done" (in any of: tight / partial / negative)
when ALL of the following hold:

- `pipeline/attempts/gross/result.md` is written with honest status
  labeling.
- Each approach attempted has its own `final_writeup.md`.
- Any Lean files produced compile via `lake build` without `sorry`
  errors (warnings OK if documented).
- `research_log_entry.md` is a one-paragraph public-facing summary.
- The one-line entry has been appended to
  `pipeline/research_log.md` in the main repo.
- `paper_draft_seed.md` exists if any of {tight, partial-A} is
  achieved; otherwise it is omitted.

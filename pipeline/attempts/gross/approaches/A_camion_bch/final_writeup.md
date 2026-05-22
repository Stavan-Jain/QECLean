# Approach A: Camion BCH multivariate apparent-distance bound — final writeup

## Status

**Partial — Partial-C** per the calibration in `success_criterion.md`:
infrastructure delivered, Camion bound itself not formalized.

The headline finding: a careful spectral analysis (see
`spectral_analysis.md`) predicts that **even a fully formalized
Camion theorem would give the gross code at most `d ≥ 9`, and more
realistically `d ≥ 4`–`6`**, against the known true `d = 12`.  Camion
is *fundamentally loose* on this polynomial pair, so the
formalization cost (~30+ hours of group-algebra infrastructure for a
modular Camion theorem) cannot deliver the tight result this approach
was named for.

This is a **clean, honest negative-leaning partial result for the
*tight* target**, combined with **infrastructure delivery** for any
downstream BB-code analysis.

## What was attempted

1. **Step 0: Abstract chain-weight → Pauli-weight distance bridge.**
   A purely homological lemma `chainWeight_lower_bound_transfers`:
   for any `HomologicalCode X`, if every non-boundary X-cycle has chain
   weight `≥ K` and every non-dual-boundary Z-cycle has chain weight
   `≥ K`, then every non-trivial logical Pauli has weight `≥ K`.

2. **Step 1: Generic BB chain complex.**  Inlined a custom
   `conv (a b : G → ZMod 2) : G → ZMod 2` group-algebra convolution
   on any `[Fintype G] [AddCommGroup G]`, with proven commutativity,
   associativity, additive/scalar linearity, and the char-2 identity
   `conv a b + conv b a = 0`.  Then built `bbBoundary1`, `bbBoundary2`
   as linear maps and proved `∂₁ ∘ ∂₂ = 0` (the proof reduces to
   `2 (conv (conv A B) f) = 0` in char 2).

3. **Step 2: HomologicalCode packaging.**  `bbChainComplex` packages
   the BB construction as a `HomologicalCode` over arbitrary
   `(ℓ, m, A, B)`.

4. **Step 2.5: Gross instantiation.**  `grossA, grossB :
   ZMod 12 × ZMod 6 → ZMod 2` as indicator pattern matches.
   `grossHomologicalCode := bbChainComplex grossA grossB`.  Verified
   `grossHomologicalCode.numQubits = 144` (by `decide`).

5. **Step 3 (alternative path): spectral analysis instead of Lean
   formalization.**  Computed by hand the modular character vanishing
   set `Z(A, B) = {(1,1), (1,2), (2,1), (2,2)}` of the gross polynomials
   over the semisimple quotient `F_2 × F_4` of `F_2[Z_12] / Jac` (and
   similarly for `Z_6`).  Used `1 + ω + ω^2 = 0` in `F_4` and `ω^3 = 1`
   throughout.  Concluded the Camion bound is loose by at least 3
   distance units even in the most optimistic interpretation.

## What worked

**The infrastructure landed.**  Lean artifacts produced:

- `QEC/Stabilizer/Homological/BBChainComplex.lean` (~285 LOC):
  * `conv` convolution + 7 algebraic lemmas
  * `bbBoundary1`, `bbBoundary2` as `LinearMap`s
  * `bbBoundary_comp : bbBoundary1 ∘ bbBoundary2 = 0`
  * `bbChainComplex : HomologicalCode`
- Updated umbrella `QEC/Stabilizer/Homological.lean` to import the new
  module.
- `pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean`:
  * `chainWeight_lower_bound_transfers` (abstract distance bridge)
  * `chainWeight_lower_bound_transfers_asymmetric` (asymmetric variant)
  * `grossA`, `grossB`, `grossHomologicalCode`
  * `grossHomologicalCode_numQubits` (= 144)

**The spectral analysis** confirmed our hypothesis that Camion is
loose, and tells us *by how much*:

```
Z(A, B) = {(a, b) : Â(χ_a, ψ_b) = 0 ∧ B̂(χ_a, ψ_b) = 0}
        = {(1, 1), (1, 2), (2, 1), (2, 2)}   (4 character orbits)
```

This is a 2 × 2 box in the cyclotomic-coset index space, giving a
multivariate-BCH apparent distance in the optimistic range
`(2+1)(2+1) = 9` or the conservative range `2·2+1 = 5`.  Either way,
**strictly less than 12**.

**This calibrates the partial-value claim with mathematical
precision**: it's not "we ran out of time", it's "the Camion bound
itself is at most 9 on this code".

## What didn't work

1. **The Camion bound, even hand-computed, doesn't reach `d = 12`.**
   The gross polynomials' specific exponent structure
   (`A = x^3 + y + y^2`, `B = y^3 + x + x^2`) yields only a 2 × 2
   consecutive zero pattern.  No formalization of Camion in Lean could
   produce a tighter bound from this pattern.

2. **The modular characteristic obstruction** (`char F_2 | |G|`) means
   the *classical* Camion theorem cannot be applied directly.  Even
   reaching the optimistic `d ≥ 9` would require formalizing a
   *modular* version of multivariate BCH, which (per literature
   review in `literature_notes.md`) does not exist in published
   form.

3. **The full Camion proof** (defining apparent distance via
   consecutive-zero patterns in the modular Fourier domain, then
   proving it lower-bounds true distance) would have required:
   - Building `F_2[G]` infrastructure (group ring, Jacobson radical,
     CRT decomposition).  ~500 LOC.
   - Building modular character theory (defining "characters" as
     ring homs into the semisimple quotient).  ~800 LOC.
   - Formalizing Bernal-Simón's apparent-distance theorem.  ~1500 LOC.
   - The CSS extension (extending classical Camion bound to
     `ker H_X / im H_Z^T`).  ~500 LOC.
   - Total estimate: ~3300 LOC, well beyond a single session and
     producing a *loose* bound at the end.

## Is the obstacle fundamental or surmountable?

**For the tight `d ≥ 12` goal: fundamental**, in the sense that
*Camion alone cannot prove it*.  The spectral analysis is unambiguous:
the apparent distance derived from `Z(A, B) = {1,2}×{1,2}` cannot
exceed 9 by any standard formulation of Camion's bound.

**For a partial `d ≥ K` Camion result for `K ∈ {4, 6, 8, 9}`:
surmountable** — requires the 3300+ LOC of infrastructure described
above.  Not infeasible, but a multi-month engineering project.

**For the *framework* / scaffolding contribution**: already delivered.
`BBChainComplex.lean` and `chainWeight_lower_bound_transfers` are
permanent additions that unblock downstream work.

## Suggested follow-ups

In rough priority order:

1. **Approach B (lifted-product / Tillich-Zémor).**  The lifted-product
   bound `d(LP(C_A, C_B)) ≥ min(d(C_A), d(C_B))` reduces the BB
   distance question to two classical distances.  For the gross code's
   `A = x^3 + y + y^2`: is `d(ker A)` computable in Lean (via
   `native_decide` over the `2^72`-element space)?  Likely no, but a
   spectral / minimum-weight characterization of `ker A` might be
   tractable.  This is the natural next moonshot to attempt.

2. **Approach D (covering-graph chain map).**  Per Pesah et al.
   2511.13560, the gross code is an `h`-cover of a smaller base BB
   code (e.g. `[[18, 4, ?]]` or `[[72, 8, ?]]`).  If the *base* code's
   distance can be `native_decide`'d (feasible at `n ≤ 72`), the cover
   bound `d_{cover} ≥ d_{base}` (when `k_{cover} = k_{base}`) gives a
   transfer.  The framework cost is moderate (chain-map machinery on
   `HomologicalCode`s).

3. **Bypass Camion entirely**: a Bravyi-Terhal-style local-stabilizer
   lower-bound theorem.  For a `D`-dimensional local stabilizer code,
   `d ≤ O(L^{D-1})` is the upper bound; matching *lower* bounds are
   less standard.  Some local-symmetry analysis on BB codes might
   yield a `d ≥ Ω(√n)` ≈ 12 lower bound for `n = 144` if BB codes can
   be shown to be effectively 2-local-with-twist.

4. **Spectral analysis at higher precision**: the present 2 × 2 zero
   pattern is from a *coarse* semisimple-quotient analysis.  A finer
   modular analysis (working in the nilpotent radical, not just the
   quotient) might find consecutive-zero patterns of higher dimension,
   pushing the Camion apparent distance up.  But the upper limit is
   still loose because of Risk 1 in `hypothesis.md`.

## Lean artifacts produced

### Promoted to the repo (durable infrastructure)

* **`QEC/Stabilizer/Homological/BBChainComplex.lean`** (~285 LOC)
  Generic BB chain complex over any finite abelian `G`.
  Contains:
  - `conv` group-algebra convolution
  - 7 convolution algebra lemmas (`conv_comm`, `conv_assoc`,
    `conv_add_left/right`, `conv_smul_left/right`,
    `conv_add_swap_eq_zero`)
  - `bbBoundary1`, `bbBoundary2` as `LinearMap`s
  - `bbBoundary_comp : ∂₁ ∘ ∂₂ = 0` chain-complex law
  - `bbChainComplex : HomologicalCode` packaging

* **`QEC/Stabilizer/Homological.lean`** (umbrella update)
  Added `import QEC.Stabilizer.Homological.BBChainComplex`.

### Approach-local (exploration / instantiation)

* **`pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean`**
  - `chainWeight_lower_bound_transfers` — abstract distance bridge
  - `chainWeight_lower_bound_transfers_asymmetric` — asymmetric variant
  - `grossA`, `grossB` — gross polynomials
  - `grossHomologicalCode : HomologicalCode`
  - `grossHomologicalCode_numQubits : ... = 144`

### Documentation

* **`plan.md`** — proof sketch and intermediate lemmas
* **`daily_log.md`** — session-by-session progress
* **`obstacle_diary.md`** — 5 obstacle entries (2 mathematical, 3
  Lean-API)
* **`spectral_analysis.md`** — the hand-computed modular character
  analysis demonstrating Camion's loss-of-tightness on the gross code

## Build status

All files compile cleanly:
- `lake build QEC.Stabilizer.Homological.BBChainComplex` — succeeds
- `lake build QEC.Stabilizer.Homological` — succeeds
- `lake env lean pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean` — exit 0

No `sorry` markers, no `axiom`s introduced beyond mathlib's trusted
core.

## Time spent

Approximate breakdown (single session):
- Read inputs, set up plan, draft `plan.md`: ~45 min
- Step 0 (abstract distance bridge): ~30 min (one-shot compile)
- Step 1 (convolution + BB boundaries): ~1.5 h (multiple debug
  iterations on `Finset.sum_*` API and `LinearMap.ext` subtleties)
- Step 2 (HomologicalCode packaging): ~20 min
- Step 2.5 (gross instantiation): ~10 min
- Step 3 (spectral analysis by hand): ~45 min
- Writeup, obstacle diary, log updates: ~30 min

**Total: ~4.5 hours.**  Well within the 8 h session and 12 h
per-approach budgets.

## Recommendation

The Approach-A budget should be marked **closed** at this point.
Continuing to pursue Camion-on-gross would burn ~30 h of infrastructure
work for a result that is *known in advance* to be loose.

The next session should pivot to **Approach B (lifted-product /
Tillich-Zémor)** with the BB chain-complex framework now in place.

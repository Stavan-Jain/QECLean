# Approach A: Camion BCH multivariate apparent-distance bound — final writeup

## Status

**Partial — Partial-C** per the calibration in `success_criterion.md`:
infrastructure delivered, Camion bound itself not formalized, and no
Lean theorem about `grossCode.distance` was produced.

The qualitative finding: a hand-computed spectral analysis (see
`spectral_analysis.md`) identifies a small joint-vanishing structure
(`Z(A, B) = {1,2} × {1,2}` — a 2×2 box) for the Gross polynomial pair
under the F₂-character group of `Z_12 × Z_6`. Heuristically, this
structure suggests that any multivariate-BCH apparent-distance bound
derivable from this consecutive-zero pattern would land well below
the empirical `d = 12` — **single-digit values are plausible, but the
precise bound is not derived in this writeup**.

This finding is **qualitatively consistent with folklore**: BB-code
distances are routinely certified by SAT/MIP solvers rather than
algebraic arguments (cf. Otjens 2025, arXiv:2502.17052, which
explicitly notes no closed-form analytical lower bound for BB codes),
so the broader claim "algebraic bounds are loose on numerically-
optimized BB codes" is widely understood. What this analysis adds is
the **specific zero-pattern computation** for the Gross polynomials;
it does **not** add a rigorous numerical upper bound on the
apparent distance, because the modular multivariate-Camion theory
(needed when `char(F) | |G|`, as here with `2 | 72`) has not been
worked out in published form.

The pragmatic conclusion (driving this approach's closure): even with
the multivariate-modular theory rigorously developed (~30+ hours of
group-algebra infrastructure), the structural prediction is that
Camion would not reach `d ≥ 12`. Continuing to formalize a bound
heuristically expected to be loose is a poor use of moonshot budget.

This is a **negative-leaning partial result for the tight target**,
combined with **durable Lean infrastructure delivery** for any
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
   formalization.**  Computed by hand the joint character vanishing
   set `Z(A, B) = {(1,1), (1,2), (2,1), (2,2)}` of the Gross
   polynomials over the semisimple quotient `F_2 × F_4` of
   `F_2[Z_12] / Jac` (and similarly for `Z_6`). Used
   `1 + ω + ω^2 = 0` in `F_4` and `ω^3 = 1` throughout. The
   computation itself is rigorous and easily verifiable; the
   **heuristic conclusion** that the resulting Camion apparent
   distance lands in single digits (and so cannot match the
   empirical `d = 12`) follows folklore reasoning but is **not
   derived as a theorem here** — see the "Limitations" section.

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

**The spectral analysis** computed the joint vanishing set of the
Gross polynomials under the F₂-Fourier transform:

```
Z(A, B) = {(a, b) : Â(χ_a, ψ_b) = 0 ∧ B̂(χ_a, ψ_b) = 0}
        = {(1, 1), (1, 2), (2, 1), (2, 2)}   (4 character orbits)
```

This `Z(A, B)` computation is **rigorous and verifiable**: it follows
mechanically from `u³ = 1` for all `u ∈ {1, ω, ω²} ⊆ F₄` (since F₄
has 3 nonzero elements) plus `1 + ω + ω² = 0` in F₄, giving
`Â = 1 + v + v²` (independent of `u`) and symmetrically
`B̂ = 1 + u + u²` (independent of `v`). The joint-vanishing
structure is then a 2 × 2 box.

What the 2 × 2 box **suggests heuristically**: a multivariate-BCH
apparent distance derived from a consecutive-zero pattern of this
small size would land in the single digits — `spectral_analysis.md`
gives a heuristic range of `[3, 9]` based on the cyclotomic-coset
structure, with most-likely value `4`–`6`. The exact numerical
bound is **not derived**; it is estimated from the structural pattern.

What the 2 × 2 box does **not** rigorously give: a derived numerical
upper bound on the modular-Camion apparent distance. The classical
Camion theorem requires `gcd(char(F), |G|) = 1` for its semisimple
Fourier setup; here `2 | 72 = |Z_12 × Z_6|`, so a modular version of
multivariate BCH is needed, and (per the literature dive) this
modular case has not been worked out in published form.

**Qualitative reading**: the small `Z(A, B)` is consistent with
folklore that algebraic bounds are loose on the Gross code — but
"loose by at least 3 distance units" is a folklore-grade statement,
not a derived theorem of this analysis.

## What didn't work

1. **The Camion bound is heuristically too small to reach `d = 12`.**
   The Gross polynomials' specific exponent structure
   (`A = x^3 + y + y^2`, `B = y^3 + x + x^2`) yields only a 2 × 2
   consecutive zero pattern, which (consistent with folklore on
   abelian-code algebraic bounds) heuristically constrains the
   apparent-distance derivation to small values. We did not formalize
   the multivariate-modular Camion theorem far enough to produce a
   rigorous numerical upper bound, so the "Camion can't reach 12"
   claim rests on the structural intuition, not a theorem in this
   writeup.

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

**For the tight `d ≥ 12` goal: heuristically fundamental.** The
spectral analysis identifies a 2 × 2 zero structure in the joint
vanishing set, and standard multivariate-BCH apparent-distance bounds
derived from such small consecutive-zero patterns produce single-digit
values. We do not have a rigorous theorem proving "Camion cannot
exceed 9 on this code" — we have a structural prediction consistent
with folklore.

**For a partial `d ≥ K` Camion result for `K ∈ {4, 6, 8, 9}`:
surmountable but expensive** — requires the 3300+ LOC of
infrastructure described above, which also includes formalizing the
modular multivariate-Camion theory (not yet in published form). Not
infeasible, but a multi-month engineering project producing a result
*heuristically expected* to be much smaller than 12.

**For the *framework* / scaffolding contribution**: already delivered.
`BBChainComplex.lean` and the `chainWeight_lower_bound_transfers`
combinator (now lifted to `Homological/Distance.lean`) are permanent
additions that unblock downstream work, independent of any specific
distance bound.

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
* **`spectral_analysis.md`** — the hand-computed character analysis
  of the joint vanishing set `Z(grossA, grossB)`, plus a heuristic
  estimate (not a derived theorem) of the corresponding multivariate-
  BCH apparent-distance range

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
Continuing to pursue Camion-on-Gross would burn ~30 h of
infrastructure work for a result that is *heuristically expected in
advance* to be loose. The structural prediction is folklore-grade
rather than theorem-grade, but it's consistent enough with the
broader literature on BB-code algebraic bounds (Otjens 2025,
Lin-Pryadko 2023) that investing further in this specific approach
is hard to justify.

The next session should pivot to **Approach B (lifted-product /
Tillich-Zémor)** with the BB chain-complex framework now in place.

## Limitations of this analysis

To be explicit about what this writeup does and does not claim:

- The `Z(grossA, grossB)` calculation is **rigorous** and easily
  verifiable. Anyone with the F₂-Fourier framework can reproduce it
  in ~30 minutes. It is not a novel mathematical technique; it is a
  routine application of decades-old machinery (Camion 1971;
  Bernal-Bueno-Carreño-Simón 2014–2024 multivariate BCH) to a
  specific polynomial pair. As a written-down result for the Gross
  polynomials specifically, it does not appear in the literature my
  dive surfaced, but the surrounding folklore is well-established.
- The qualitative conclusion "Camion is loose on the Gross code" is
  **consistent with folklore but not derived as a theorem here**.
  Researchers working on BB codes informally understand algebraic
  bounds don't reach numerical distances — IBM's MIP-based
  certification of `d = 12` is the standard, and no closed-form
  analytical lower bound is known.
- The specific numerical claim "Camion ≤ 9 on Gross" is a
  **heuristic estimate**, not a theorem. A rigorous derivation would
  require the modular multivariate-Camion theory worked out
  explicitly (the classical theorem requires `gcd(char(F), |G|) = 1`,
  which fails here), which has not been done in published form. The
  `[3, 9]` heuristic range in `spectral_analysis.md` is a structural
  intuition, not a theorem.
- **No Lean theorem about `grossHomologicalCode.distance` was
  produced.** The Lean artifacts are infrastructure (BB chain complex
  + abstract CSS-bridge combinator), not distance results.

A future, more rigorous version of this analysis would either:
(a) work out the modular multivariate-Camion bound and derive a
rigorous numerical upper bound, then formalize in Lean; or
(b) be content with the folklore framing and proceed directly to
Approach B without further investment in Camion-specific machinery.
This writeup commits to (b).

# Hypothesis: gross code (IBM [[144,12,12]] Bivariate Bicycle)

## Target

- **Code**: gross code, the [[144, 12, 12]] Bivariate Bicycle (BB) code.
- **Construction**: CSS code with check matrices `H_X = [A | B]`,
  `H_Z = [B^T | A^T]` over the group algebra `F_2[Z_12 × Z_6]`, where
  - `A(x, y) = x^3 + y + y^2`,
  - `B(x, y) = y^3 + x + x^2`,
  with relations `x^12 = y^6 = 1`, `xy = yx`. Each block of `H_X`, `H_Z`
  is `72 × 72`, so `n = 144`, `k = 12`, target `d = 12`.
- **Distance claim to verify**: `d ≥ 12` (tight) or any `d ≥ K` with `K ≥ 2`
  (partial).
- **State of the art proof method**: **Mixed integer programming** (per
  Bravyi-Cross-Gambetta-Maslov-Rall-Yoder, Nature 2024). The published
  `d = 12` is an MIP-solver output, not an analytical proof. **No
  closed-form analytical lower bound exists** in the literature for this
  polynomial pair (confirmed via Otjens 2502.17052 and Lin-Pryadko
  2306.16400 surveys).

## Hypothesis

A **Camion-style multivariate BCH apparent-distance bound, extended from
classical abelian codes to quantum CSS abelian codes**, reduces the
problem of lower-bounding the gross code's distance to a finite
combinatorial computation on consecutive-zero patterns in the
discrete-spectrum representation of `F_2[Z_12 × Z_6]`.

Concretely, the hypothesis claims:

> There is a Lean-formalizable theorem of the form: for any abelian
> CSS code defined over `F_2[Z_ℓ × Z_m]` by polynomial pair `(A, B)`,
> the minimum distance `d` satisfies `d ≥ d_app(A, B; Z_ℓ × Z_m)`,
> where `d_app` is a computable invariant defined via consecutive-zero
> patterns in the spectral decomposition of the dual code's generator
> ideal. For the gross polynomial pair specifically, `d_app` evaluates
> (mechanically) to some explicit integer.

We are **honest** that we expect `d_app(gross) ∈ {2, 4, 6, 8}` —
likely *loose* against the true `d = 12`. But the **parametric Lean
theorem** would be a first-of-its-kind formalization: no analytical
lower-bound machinery for BB codes is in the literature, and the
Camion-quantum extension itself is novel mathematical work that
deserves formalization.

## Prior art

- **Camion 1971** (MRC Technical Report #1059, "Abelian Codes"):
  introduced the apparent distance of an abelian code, generalizing the
  cyclic BCH bound to `F_q[G]`-ideal codes for finite abelian `G`. The
  apparent distance is a lower bound on the true minimum distance via a
  Fourier / consecutive-zero argument.
- **Bernal-Bueno-Carreño-Simón 2014** (CACTC 2014, "A notion of
  multivariate BCH bounds and codes"): algorithmic procedure to compute
  the apparent distance for multivariate (e.g. 2D over `Z_ℓ × Z_m`)
  abelian codes via hypermatrix manipulations. Linear-complexity
  algorithm for the 2D case. **Defines** a "BCH multivariate code" as
  one whose true distance equals the apparent distance (bound is tight).
- **Bernal-Simón 2024** (arXiv:2402.03938, IEEE TIT, "Apparent Distance
  and a Notion of BCH Multivariate Codes"): the modern formalization
  reference. Best paper to translate to Lean for the **classical**
  Camion theory.
- **Lin-Pryadko 2023** (arXiv:2306.16400, "Quantum two-block group
  algebra codes"): subsumes BB codes as the abelian-2BGA case. Gives
  parameter bounds, but the lower bounds (typically `Ω(√n)`-flavored)
  are loose for IBM-optimized codes.
- **Otjens 2025** (arXiv:2502.17052, "Existence and Characterisation of
  Bivariate Bicycle Codes"): algebraic characterization via polynomial
  ideals + CRT decomposition. Computes `k` analytically. Gives an
  **upper bound** on `d` (Bravyi-Terhal-style, `O(n^{1-1/D})`), but
  **no lower bound** — confirms our literature gap.
- **Cao et al. 2025** (arXiv:2503.04699): uses BKK theorem on Newton
  polytopes to compute `k`. Does *not* address `d`.
- **Pesah et al. 2025** (arXiv:2511.13560, "Sequences of Bivariate
  Bicycle Codes from Covering Graphs"): proves relative bounds
  `d_h ≥ d`, `d_h ≤ h·d` for covers; uses chain-maps on homology.
  Compatible with our `Stabilizer/Homological/` framework but requires
  a *base* `d` as input.
- **Bravyi et al. Nature 2024** (arXiv:2308.07915): introduces the
  gross code; certifies `d = 12` by **mixed-integer programming**
  (computational, not analytical). No analytical lower bound.

**Why standard approaches don't suffice**: every published technique
either (a) gives the right *dimension* `k` but not `d` (BKK, Otjens), or
(b) gives an asymptotic `Ω(√n)` *existence* bound that doesn't pin down
`d` for any specific polynomial pair (Lin-Pryadko, Tillich-Zémor lifted
product), or (c) requires a *base-case distance* that itself is hard
(covering-graph chain maps).

## Why this might work

1. **Bivariate Bicycle codes have an abelian symmetry** built in: the
   group `Z_12 × Z_6` acts on the chain complex commuting with both
   boundary maps. This is precisely the setting where Camion-style
   character/Fourier decomposition theorems were designed to apply.
2. **The CRT decomposition** `F_2[Z_12 × Z_6] ≅ ∏_χ F_2[χ-isotype]`
   (using `Z_12 ≅ Z_4 × Z_3` and the factorizations of `x^12 - 1`,
   `y^6 - 1` over `F_2`) is **computable** and small enough to
   manipulate by hand — about a dozen irreducible-isotype components.
3. **Camion's framework is well-developed classically** (50+ years of
   theory), and the Bernal-Simón 2014 algorithm gives an explicit
   linear-complexity procedure. We're not inventing the classical
   bound; we're (a) formalizing it in Lean and (b) extending to CSS.
4. **The CSS extension is the *only* truly novel piece**. The classical
   Camion bound applies to the constituent classical codes `C_X = ker
   H_X` and `C_Z = ker H_Z`; the CSS distance equals the minimum-weight
   element of `C_X \ im H_Z^T` (the "non-trivial logical X-cycles"). A
   careful CSS extension takes the classical Camion bound on `C_X`
   *together* with a coset-correction term for `im H_Z^T`.
5. **Our existing `Stabilizer/Homological/` framework is the right
   abstraction layer**. `xChainOf` extracts the X-support 1-chain;
   `chainWeight` measures its size; `weight_ge_chainWeight_xChainOf`
   already establishes the central inequality. Adding a *lower* bound
   on `chainWeight c` for `c ∈ ker ∂_1 \ im ∂_2` is exactly the
   missing step, and Camion is the candidate machinery.

## Why this might fail

This is the honest part. We list specific risks, not vague worries.

### Risk 1: Camion is *known* to be loose for codes with engineered distance.
The gross code was numerically discovered/optimized, not algebraically
designed. There is no a priori reason its apparent distance should be
close to `12`. Heuristic estimates (informally; without computation):
the gross polynomials `A = x^3 + y + y^2`, `B = y^3 + x + x^2` have
*sparse* exponent sets (three monomials each, low-degree), which tends
to give *short* consecutive-zero patterns in the spectrum — and short
patterns mean *small* apparent distance.

**Concrete worry**: `d_app(gross)` might be as low as `2` or `4`.
Outcome: a "first analytical lower bound `d ≥ 2`" formalization is
honest but uninspiring.

### Risk 2: Modular characteristic obstruction.
`F_2[Z_12 × Z_6]` has `char(F_2) = 2` and `|Z_12 × Z_6| = 72 = 2^3 ·
3^2`. Since `2 | 72`, the group algebra is **not semisimple** by
Maschke's theorem. The clean character / DFT decomposition that
Camion uses in characteristic-zero or `gcd(|G|, char) = 1` cases needs
to be replaced by **CRT decomposition over irreducible factors of
`x^12 - 1` and `y^6 - 1` in `F_2[x]` and `F_2[y]`** — a more delicate
analysis. Otjens (2502.17052) handles this CRT for `k`, but the
distance side is open.

**Concrete worry**: the formalization may need to invent the "modular
Camion bound" since classical Camion typically assumes the semisimple
setting. This is more research, not less.

### Risk 3: Mathlib gaps.
- Mathlib **does have** `MonoidAlgebra` / `AddMonoidAlgebra` and `ZMod`
  basics, but **may not have** clean APIs for:
  - DFT over `Z_ℓ × Z_m` with `Z_ℓ × Z_m` realized as `ZMod ℓ × ZMod m`.
  - Irreducible factorization of `x^n - 1` over `F_2` (cyclotomic cosets).
  - Consecutive-zero patterns and BCH-bound machinery.
  Mathlib has cyclic codes (`Mathlib.LinearAlgebra.Matrix.PolyCyclic`?
  — search needed), but multivariate / abelian-group versions are
  scarcer.
- Risk: the moonshot's per-approach budget gets eaten by building
  mathlib infrastructure that should be upstreamed but isn't. We must
  guard against this by **delegating mathlib gaps to flagged
  engineering work** rather than filling them inline.

### Risk 4: Hypothesis drift.
- A common research failure mode: start trying to prove `d ≥ 12`,
  silently downgrade to `d ≥ 4`, declare partial success. We commit
  upfront to recognizing this by **logging the apparent-distance value
  the moment it is computed** in the approach, not at the end.
- If `d_app(gross) ≤ 2`, the approach is effectively a negative result
  for the headline target and we should surface that immediately, not
  press on.

### Risk 5: The CSS extension is harder than the classical theory.
- Classical Camion bounds the minimum weight of `C = ker H_X` (the full
  classical code).
- CSS distance bounds the minimum weight of `C_X \ im H_Z^T` (cycles
  modulo boundaries).
- The classical Camion bound applied to `C_X` is a *lower* bound on the
  CSS distance *only if* low-weight elements of `C_X` are *not* all
  boundaries. This requires a separate coset analysis.
- **Concrete worry**: the coset analysis may need to invoke
  character-isotype-specific apparent-distance bounds, raising the
  complexity considerably.

## Connection to existing repo abstractions

The fit with the existing repo is **strong** at the homological-code
layer and **weak** at the group-algebra / character-theory layer.

**Reusable directly**:
- `Stabilizer/Homological/Code.lean` — `HomologicalCode` struct.
- `Stabilizer/Homological/CSS.lean` — `chainXOperator`, `chainZOperator`.
- `Stabilizer/Homological/Distance.lean` — `xChainOf`, `zChainOf`,
  `chainSupport`, `chainWeight`,
  `weight_ge_chainWeight_xChainOf` / `weight_ge_chainWeight_zChainOf`.
  The Camion bound enters as a *new* lower bound on `chainWeight` of
  non-boundary cycles.
- `Stabilizer/Homological/LogicalCorrespondence.lean` — translates
  Pauli logical operators to chain-level cycles.
- `Stabilizer/Core/CodeDistance.lean` — abstract `HasCodeDistance`
  predicate.
- The packaging pattern from `Stabilizer/Codes/ToricCodeNStabilizerCode.lean`
  (trimmed generator list, `IsNontrivialLogicalOperator_of_toSubgroup_eq`
  bridge to abstract distance lemmas).

**Needs to be built** (large; would shape the moonshot's footprint):
1. `Stabilizer/GroupAlgebra/`
   - `GroupAlgebra.lean` — `F_2[G]` for finite abelian `G` as
     `MonoidAlgebra (ZMod 2) G` (mathlib has this; thin wrappers).
   - `Fourier.lean` — DFT over `Z_ℓ × Z_m`, character theory in the
     modular setting (i.e. the CRT decomposition over `F_2[x] / (x^ℓ - 1)
     · F_2[y] / (y^m - 1)`).
   - `Maschke.lean` — modular semisimple decomposition; or its absence.
2. `Stabilizer/Homological/AbelianCSS.lean` — lifting `HomologicalCode`
   to abelian-symmetric codes (i.e. carrying a `G`-action commuting with
   boundary maps).
3. `Stabilizer/Codes/BBCode.lean` — concrete BB code construction
   parametrized by `(ℓ, m, A, B)`, with `grossCode : BBCode 12 6` as the
   target instance.
4. `Stabilizer/Codes/Camion/`
   - `ApparentDistance.lean` — definition of apparent distance for
     classical abelian codes via consecutive-zero patterns.
   - `Bound.lean` — proof that apparent distance lower-bounds true
     classical minimum distance (the heart of Camion's theorem).
   - `CSSExtension.lean` — the **novel** piece: Camion bound transferred
     to CSS / `HomologicalCode` setting via the abelian symmetry of the
     chain complex.

Total LOC estimate: **~3500** for the full ambitious target (matches the
`catalog/zoo.yaml` estimate). For a *partial* result (just the
classical Camion bound + a sketch of the CSS extension), realistic LOC
is **~1500-2000**.

## Approaches I plan to try

Ordered by promise-to-cost ratio.

### Approach A: Camion's multivariate BCH bound for abelian quantum codes

**Strategy**:
1. Formalize the classical Camion apparent distance for `F_2[Z_ℓ × Z_m]`-
   ideal codes, following Bernal-Bueno-Carreño-Simón 2014 +
   Bernal-Simón 2024.
2. Prove the classical theorem: apparent distance ≤ true minimum
   distance.
3. Extend to CSS: combine the classical bound on `ker H_X` with a
   coset analysis for `im H_Z^T` to derive a *lower bound on quantum
   distance*.
4. Instantiate at the gross polynomial pair and compute
   `d_app(gross)` mechanically.
5. Tighten if possible (multiple consecutive-zero patterns, refined
   character-isotype analysis).

**Estimated time**: 10–14h for the classical formalization (Steps 1–2),
4–6h for the CSS extension (Step 3), 1–2h for the instantiation
(Step 4). Within the 12h per-approach budget if we split across two
sessions or focus on Step 4 directly with hand-proved Steps 1–3
sketches.

**Expected outcome**: `d_app(gross) ∈ {2, 4, 6, 8}`, likely `4` or `6`.

### Approach B: Lifted-product / Tillich-Zémor distance bound

**Strategy**: Express the BB code as a lifted product (tensor over the
group algebra) of two classical codes `C_A = ker A`, `C_B = ker B`.
Apply the Tillich-Zémor theorem `d(LP(C_A, C_B)) ≥ min(d(C_A), d(C_B))`
or a refined Lin-Pryadko variant.

**Concerns**:
- Requires the constituent classical distances `d(C_A)`, `d(C_B)`,
  which for `A = x^3 + y + y^2` over `F_2[Z_12 × Z_6]` are themselves
  computable but require their own argument.
- Lin-Pryadko bound is loose typically; might give `d ≥ 2` or `d ≥ 4`
  at best for this code.

**Expected outcome**: comparable to or worse than Camion. Use as a
**sanity-check** for the Camion bound; if both give the same number,
that's evidence of the apparent-distance bound being honest. If
lifted-product gives a *better* number, the Camion analysis missed
something and we should re-examine.

### Approach C: Polynomial-ideal Gröbner basis structure on `ker H_X / im H_Z^T`

**Strategy**: Extending Cao et al.'s BKK-on-Newton-polytope approach
from dimension `k` to a *minimum-weight* analysis. Open research:
Newton polytopes measure module multiplicities, not Hamming weights.
Possibly use the structure of the *initial monomials* of a Gröbner
basis of the syzygy module.

**Concerns**:
- No prior art; this is real research, not formalization of known
  mathematics.
- Mathlib has limited Gröbner-basis support; would require building.
- Low-promise for a *tight* bound; more useful for characterizing
  *which* low-weight cosets exist.

**Defer this approach** to last unless Approaches A and B both fail
informatively.

### Approach D (contingency): Covering-graph chain map + base-code distance

If a *smaller* BB code's distance can be analytically bounded (e.g. one
of the BB72 / BB90 / BB108 codes from `pipeline/cache/eczoo_data/.../bb/`),
and the gross code is an `h`-cover of that base, then the Pesah et al.
chain-map argument gives `d(gross) ≥ d(base)` (when `k_{cover} = k_{base}`).

**Concerns**:
- The gross code as a cover-of-something is plausible but not directly
  cited in the literature with the right covering structure for the
  Pesah bound to apply.
- Bottleneck shifts to finding a base BB code with analytically-known
  distance — which is the original problem one level down.

**Defer** unless A, B, C all fail and we want one more swing.

### Approach E (escape hatch): Documenting the impossibility cleanly

If A through D all hit fundamental obstacles, the moonshot's final
output is a **negative result write-up**: a detailed
`final_writeup.md` for each approach explaining *why* the Camion
extension and lifted-product extensions are loose for gross-style
polynomials. This documents the literature gap and points at what
*would* be needed (e.g. modular Maschke decomposition formalization,
or a Bravyi-Terhal-style local-stabilizer lower-bound theorem).

## Calibrated outcome bands

- **Tight (`d ≥ 12` in Lean)**: very unlikely without genuinely novel
  math. Treated as the aspirational ceiling.
- **Partial 1 (`d ≥ 4` or `d ≥ 6` via Camion, parametric in `(ℓ, m, A,
  B)`, with `grossCode` instantiation)**: most plausible outcome.
  Worth a paper at a coding-theory workshop (first analytical lower
  bound + first Lean formalization of Camion for abelian quantum codes).
- **Partial 2 (`d ≥ 2` via simplest possible argument)**: still a
  first analytical bound, but weak; would be a tech-report contribution.
- **Negative (Camion is provably loose to `d ≤ 2-4`, clean obstacle
  diary)**: very valuable for future BB research and informs the
  community that purely-algebraic bounds need a new idea.

We commit to **honest labeling** of which band we end in.

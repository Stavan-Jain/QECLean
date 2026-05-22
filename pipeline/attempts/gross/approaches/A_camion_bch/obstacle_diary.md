# Obstacle diary: Approach A (Camion BCH)

Structured log of obstacles encountered. Format:

```
## YYYY-MM-DD: <obstacle name>

**Where**: <file:line or step>
**What**: <concrete description of the issue>
**Attempted resolutions**:
- <attempt 1, outcome>
- <attempt 2, outcome>
**Status**: <resolved | blocked | deferred>
**Lesson** (if resolved): <one-liner for CLAUDE.md or future sessions>
```

---

## 2026-05-22: Modular characteristic obstacle in Camion's bound

**Where**: spectral analysis (see `spectral_analysis.md`)
**What**: `F_2[Z_12 × Z_6]` is not semisimple (`char F_2 = 2` divides
`|G| = 72`).  Camion's classical apparent-distance theorem assumes the
semisimple setting (`gcd(|G|, char) = 1`).  For the modular case, a
"modular Camion bound" needs to be developed from scratch.
**Attempted resolutions**:
- Work via the Jacobson-radical quotient `F_2[G] / Jac`: the 9
  surviving character orbits give a clean computation of the joint
  vanishing set `Z(A, B) = {(1,1), (1,2), (2,1), (2,2)}`.  Tractable.
- But the multivariate BCH bound's apparent distance formula
  (Bernal-Simón 2024) is stated for the semisimple case.  Translating
  it to the modular setting requires nontrivial new mathematics
  (orthogonality of characters fails in modular form).
**Status**: deferred (out of approach-A scope)
**Lesson**: when the polynomial group `|G|` shares a factor with the
char of the coefficient field, Camion-style bounds are at minimum 1
research paper's worth of new infrastructure away.

## 2026-05-22: Camion bound is loose on gross polynomials

**Where**: spectral analysis (see `spectral_analysis.md`)
**What**: Even *granting* a full modular-Camion theorem, the apparent
distance for the gross polynomials evaluates to `d_app ∈ [3, 9]`,
strictly less than the true `d = 12`.  This is the fundamental
"engineering-vs-algebraic" gap: the gross code was numerically
discovered by MIP optimization, not algebraically designed, so its
algebraic bounds are loose.
**Attempted resolutions**: none feasible without changing approach
**Status**: blocked — this is a fundamental obstacle for Approach A's
*tight* goal.  Approach A is recategorized as "partial".
**Lesson**: numerical-optimization-discovered codes (like gross) tend
to have inherently loose algebraic distance bounds.  The IBM team's
choice of MIP over analytical proof was not an oversight; it
reflects the actual mathematical situation.

## 2026-05-22: `Finset.sum_nbij'` unification with implicit args

**Where**: `BBChainComplex.lean:56` (original `conv_comm` proof)
**What**: `Finset.sum_nbij'` tried to unify against a goal that had
an implicit Fintype parameter, producing universe constraint errors
(`?u.1850.327+1 =?= max 1 ?u.1850.45`).
**Attempted resolutions**:
- Used `Finset.sum_bij'` instead (slight syntactic variant, no
  `Fintype` constraint inference).  Worked cleanly.
**Status**: resolved
**Lesson**: prefer `Finset.sum_bij'` over `Finset.sum_nbij'` when the
finset is `Finset.univ` — `nbij'` is for arbitrary `Finset`s and the
universe inference is finicky.

## 2026-05-22: `abel` failing on `-1 •` smul in AddGroup

**Where**: `BBChainComplex.lean:64` (and similar)
**What**: After `Finset.sum_bij'` introduces the bij goals as
`g + -1 • (g + -1 • h) = h`, `abel` fails because the `-1 • _` is in
ZMod-scalar form, not native group subtraction.
**Attempted resolutions**:
- `intro h _; simp` closes the goal cleanly (simp normalizes
  `-1 • x` to `-x` then applies group laws).
**Status**: resolved
**Lesson**: prefer `simp` for closing `Finset.sum_bij'` index-bijectivity
goals on additive groups — it handles the scalar-multiplication
normalization that `abel` chokes on.

## 2026-05-22: `LinearMap.ext` interaction with `(G → ZMod 2)` domain

**Where**: `BBChainComplex.lean:225` (bbBoundary_comp)
**What**: `ext` on a `LinearMap (G → ZMod 2) → (G → ZMod 2)`
expanded into a `LinearMap.single (ZMod 2)` form, treating
`G → ZMod 2` as `⨁_G ZMod 2`.  This made the goal unreadable
(involving `LinearMap.single`).
**Attempted resolutions**:
- Manually `refine LinearMap.ext (fun f => ?_)` first, then `ext g`
  to introduce just the per-element argument.
**Status**: resolved
**Lesson**: when `ext` unfolds too aggressively on LinearMaps with
function-space domains, fall back to explicit `LinearMap.ext` +
ordinary `ext` on the resulting function equality.


# Result: gross code [[144, 12, 12]] moonshot

## Overall status

**Partial / negative-result hybrid, two approaches closed.**

The moonshot remains open for future approaches (C / D / E from the
hypothesis), but the two natural algebraic-bound approaches have been
attempted and closed:

- **Approach A (Camion BCH multivariate)**: heuristically loose
  (partial-C: infrastructure + folklore-grade negative).
- **Approach B (Lifted-product / Tillich-Zémor)**: rigorously loose
  (negative-result: Lean-verified ceiling ≤ 3).

Neither approach delivers tight `d ≥ 12`.  Both deliver Lean
infrastructure or evidence that contributes to the broader picture.

## Distance claim verified

**No tight Lean theorem of the form
`grossHomologicalCode.distance ≥ 12` was produced.**

Approach A delivered durable infrastructure
(`QEC/Stabilizer/Homological/BBChainComplex.lean`, the abstract
`chainWeight_lower_bound_transfers` combinator) but not a specific
numerical bound.

Approach B delivered **conditional Lean theorems** showing that
*any* Statement-12-derived lower bound on Gross's distance is `< 12`:

```lean
theorem gross_TZ_loose
    (d_0 : ℕ)
    (h_TZ : TZCeilingType GrossGroup' grossA grossB d_0 gross_ℓa gross_ℓb) :
    d_0 < 12
```

This *negatively* characterizes the Statement-12 bound, not the true
distance.

## Approaches tried

| Approach | Outcome | Time spent | Key obstacle |
|---|---|---|---|
| A (Camion BCH) | partial-C | 4.5h | Camion bound heuristically ≤ 9 on Gross polynomials (modular char obstruction in F_2[G] with 2 \| 72) |
| B (Lifted-product / TZ) | negative-result | 4.75h | Statement-12 ceiling `d_0 ≤ min([G_a:N], [G_b:N]) = 3` rigorously caps the bound at 3 |

**Total moonshot time so far: 9.25h** (across two approaches, within
the 12h-per-approach and 80h-total budgets).

## What we learned

Three substantive findings emerged across the two approaches.

### 1. Algebraic bounds are structurally loose on engineered BB codes

The Gross code was numerically discovered via MIP solvers
(Bravyi-Cross-Gambetta-Maslov-Rall-Yoder 2024), not algebraically
designed.  Two natural algebraic-bound approaches — Camion's
multivariate BCH and Lin-Pryadko's Tillich-Zémor analog — both fail
to certify even `d ≥ 4` on this polynomial pair.  This is consistent
with folklore on BB-code distance certifications (they go through
SAT/MIP, not analytic arguments), but our work pins down the
specific numerical ceilings:

- **Camion ≤ 9** (heuristic estimate, based on a 2×2 joint-vanishing
  pattern of `(Â, B̂)` at the semisimple-quotient level).
- **Statement-12 / Tillich-Zémor ≤ 3** (rigorous, derived from
  Lin-Pryadko's own structural ceiling `d_0 ≤ min(ℓ_a, ℓ_b)`).

The Tillich-Zémor ceiling is **the cleanest negative result of the
moonshot so far**: a direct consequence of the support-subgroup index
arithmetic, mechanically verifiable in Lean.  It says no amount of
classical-distance computation refinement can save Approach B on
Gross.

### 2. The BB chain-complex framework is durable and reusable

The Lean infrastructure produced in Approach A (`BBChainComplex.lean`,
~285 LoC, now on main) is generic over any finite abelian `G` and any
polynomial pair `A, B : G → ZMod 2`.  Specifically, it provides:

- `conv : (G → ZMod 2) → (G → ZMod 2) → (G → ZMod 2)` — group-algebra
  convolution on abelian `G`
- `conv_comm`, `conv_assoc`, `conv_add_*`, `conv_smul_*`,
  `conv_add_swap_eq_zero` — 7 algebraic-property lemmas
- `bbBoundary1`, `bbBoundary2` — `LinearMap`s
- `bbBoundary_comp : bbBoundary1 ∘ bbBoundary2 = 0` — chain-complex law
- `bbChainComplex : HomologicalCode` — packaging

Plus `chainWeight_lower_bound_transfers` (`Distance.lean`), an
abstract CSS distance-bridge combinator that converts a lower bound on
non-boundary cycles' chain weight into a lower bound on Pauli
operator weight.

This infrastructure is **independent of any specific distance bound**
and remains useful for:
- Future BB-code analyses (different `(ℓ, m, A, B)` parameters)
- Hypergraph-product codes (analogous structure)
- Any homological-CSS-code with abelian symmetry

### 3. The specific Lin-Pryadko index ceiling for Gross is a publishable observation

The Tillich-Zémor ceiling `d_0 ≤ min(ℓ_a, ℓ_b)` is stated in the
Lin-Pryadko 2023 paper (Sec. IV.F, p. 8) but not (to our knowledge)
applied explicitly to the Gross polynomial pair anywhere in print.
Our `attempt.lean` computes the index parameters
`ℓ_a = ℓ_b = 3` mechanically and packages the result as
`gross_TZ_loose : d_0 < 12`.  This is a small, sharp observation
suitable for a research-note or workshop-track contribution.

### 4. Honest calibration: what we did NOT achieve

- No tight `d ≥ 12` Lean theorem for the Gross code.
- No formalization of Camion's multivariate-BCH apparent-distance
  theorem (estimated ~1500 LoC; not pursued due to predicted
  looseness).
- No formalization of Lin-Pryadko Statement 12 itself (estimated
  ~500 LoC; not pursued due to predicted-and-now-verified
  looseness).
- No computation of the constituent classical distances
  `d_A^⊥, d_B^⊥` (irrelevant given the index ceiling).

## Lean artifacts

### Promoted to the repo (durable infrastructure, on main)

* `QEC/Stabilizer/Homological/BBChainComplex.lean` (~285 LoC)
  Generic BB chain complex over finite abelian `G`.
* `QEC/Stabilizer/Homological/Distance.lean` (extended)
  Added `chainWeight_lower_bound_transfers` and asymmetric variant.
* `QEC/Stabilizer/Homological.lean` (umbrella)
  Added `import QEC.Stabilizer.Homological.BBChainComplex`.

### Approach-local (exploration / verification)

* `pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean`
  Gross instantiation: `grossA`, `grossB`, `grossHomologicalCode`,
  numQubits = 144.
* `pipeline/attempts/gross/approaches/B_lifted_product/attempt.lean`
  Support subgroup arithmetic + Statement-12 ceiling for Gross
  (Lean-verified by `decide`).  Conditional theorem
  `gross_TZ_loose : d_0 < 12`.

### Documentation

* `pipeline/attempts/gross/hypothesis.md`
* `pipeline/attempts/gross/budget.yaml`
* `pipeline/attempts/gross/success_criterion.md`
* `pipeline/attempts/gross/partial_value.md`
* `pipeline/attempts/gross/literature_notes.md`
* `pipeline/attempts/gross/state.yaml` (current status)
* `pipeline/attempts/gross/approaches/A_camion_bch/{plan,daily_log,obstacle_diary,spectral_analysis,final_writeup}.md`
* `pipeline/attempts/gross/approaches/B_lifted_product/{plan,daily_log,obstacle_diary,spectral_pre_check,final_writeup}.md`

## Patterns to lift into CLAUDE.md

### One-line entries worth promoting

- **Pattern: enumerated-Finset support subgroups for `decide`-driven
  arithmetic.**  For `ZMod ℓ × ZMod m` (small `ℓ, m`), defining
  subgroups as `Finset.image (...)` over `Finset.range × Finset.range`
  makes cardinality and intersection facts `decide`-closable in milliseconds.
  See `attempt.lean` in `B_lifted_product` for the pattern.

- **Pattern: conditional moonshot theorems via `TypeProp`-style
  signatures.**  When a published theorem is heavy to formalize but
  its *consequences* are easy to derive, state the theorem as a
  `def TZCeilingType := P → Q → ... → R` and prove the implication
  with the consequence concrete.  This delivers Lean evidence for
  the implication without paying the full formalization cost.

### Mathlib API drift caught

- `Mathlib.GroupTheory.Subgroup.Basic` has moved to
  `Mathlib.Algebra.Group.Subgroup.Basic` (v4.30).

## Recommended next steps

For the human reviewer / next session:

### Highest priority

1. **Approach C/D** (covering-graph chain maps; Pesah 2025
   arXiv:2511.13560).  The gross code is a cover of a smaller BB
   code per the paper; if the base code's distance can be bounded
   analytically (or `native_decide`'d on small `n`), the cover
   theorem `d_cover ≥ d_base` transfers.  This is the **single most
   promising remaining approach** for the gross moonshot.  Estimated
   ~1000 LoC framework + concrete instantiation.

2. **Document the Lin-Pryadko ceiling discovery for the BB-code
   community.**  The `≤ 3` ceiling on Gross is a sharp,
   publishable observation.  Worth a short research note (~5-10
   pages: Camion ≤ 9 from Approach A + Tillich-Zémor ≤ 3 from
   Approach B + the Lean verification artifacts).  Workshop-level
   contribution, not full-paper.

### Lower priority (defer or skip)

3. **Approach C (Gröbner-basis ideal-structure)** from the original
   hypothesis.  Estimated cost is high (Gröbner basis machinery does
   not exist in mathlib at the level needed), and there's no prior
   art for distance bounding via this route.  Defer until other
   approaches are exhausted.

4. **Approach E (write-up the impossibility)** — already partially
   done by virtue of Approaches A and B's negative results.  Could
   be elevated to a full negative-result paper if Approaches C/D
   also fail.

## Publishability assessment

**Workshop-level note (e.g. ITC 2026, ISIT short paper, or Quantum
arXiv tech report).**

The publishable observations:
1. Camion multivariate BCH apparent-distance bound on the Gross
   polynomial pair, plus a hand-derived structural prediction that
   it's `≤ 9`.
2. Lin-Pryadko Statement-12 / Tillich-Zémor analog applied to Gross,
   with a rigorous derivation that it's `≤ 3`.
3. Lean formalization of the index arithmetic, providing a
   reproducible verification artifact.

These together form a coherent **negative-result note**: "Two
natural algebraic approaches to BB-code distance certification fail
on the IBM Gross code, by structural arguments we derive and
verify in Lean."  Not a full paper, but a publishable note
documenting a literature gap.

The Lean infrastructure (`BBChainComplex.lean`) is independently
useful and could be cited as a separate "Lean formalization
contribution" if pursued.

**Not publishable yet**: any tight `d ≥ 12` Lean theorem.  This
remains the moonshot's aspirational target, contingent on a
non-algebraic technique (covering-graph chain maps, or genuinely
novel math).

## Status of remaining approaches (per `hypothesis.md`)

| Approach | Status | Decision |
|---|---|---|
| A (Camion BCH) | Closed: partial-C | Continued investment not justified (heuristically loose) |
| B (Lifted-product / TZ) | Closed: negative-result (rigorous) | Continued investment not justified (rigorously loose by ≤ 3) |
| C (Gröbner basis) | Not attempted | Defer (high cost, no prior art) |
| D (covering-graph chain map) | Not attempted | **Recommended next** (most promising remaining) |
| E (impossibility write-up) | In progress | Already realized by Approaches A + B; promote to formal note if C/D also fail |

**State**: moonshot has not exhausted approaches.  Approach D
(covering-graph chain maps) is the natural next session's target.

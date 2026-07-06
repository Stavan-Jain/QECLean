# Informal spec: CSS code concatenation `[[n₁·n₂, k₂, ≥ d₁·d₂]]`

> **Status: plan only.** No Lean skeleton has been drafted. All Lean
> signatures below are *design-level proposals* to be refined at Stage 2,
> not verified code. Existing-API references were spot-checked against the
> repo on 2026-06-15 (see `reuse_audit.md`).

## Summary

**Concatenation** builds a stronger stabilizer code by encoding recursively:
the physical qubits of an *outer* code become the logical qubits of an
*inner* code. Take an inner CSS code `[[n₁, 1, d₁]]` and an outer CSS code
`[[n₂, k₂, d₂]]`. Replace each of the `n₂` qubits the outer code acts on by
one *logical* qubit of the inner code — i.e. a block of `n₁` physical qubits.
The composite is a CSS code

```
[[ n₁·n₂,  k₂,  ≥ d₁·d₂ ]]
```

on `n₁·n₂` physical qubits, indexed as blocks `(b : Fin n₂, i : Fin n₁)`.

This attempt formalizes (a) a parametric `concatenate` **constructor**
producing a valid `StabilizerCode (n₁·n₂) k₂`, and (b) the **distance lower
bound** `HasCodeDistance (concatenate D) (d₁·d₂)`, made tight by an explicit
weight-`d₁·d₂` witness. The validating concrete instance is Steane⊗Steane
`= [[49, 1, 9]]`.

## Scope and assumptions (fixed)

- **CSS-only**, both inner and outer. Drives every typing / no-`−I` /
  identity-operator argument and lets promotion skip the `Y` branch.
- **k₁ = 1** (exactly one inner logical qubit). Load-bearing at: the induced
  outer object is *one* outer Pauli class per block; the canonical single
  `X̄₁ / Z̄₁` pair; the single inner distance witness. Generalizing to k₁ ≥ 2
  is explicitly out of scope.
- **Distance is a lower bound made tight by a witness.** `HasCodeDistance`
  (`CodeDistance.lean:28`) is "min weight of a nontrivial logical." We prove
  `d ≥ d₁·d₂` for every nontrivial logical *and* exhibit one of weight exactly
  `d₁·d₂`; together these give `HasCodeDistance (concatenate D) (d₁·d₂)` on
  the nose. We do not separately claim more.
- **Inner code: parametric, validated on fixed Steane.** The constructor is
  parametric in `Cin`/`Cout`; the hard lemmas concern `embedBlock`/`promote`
  structure, not a specific generator table. Steane is the M7 instance because
  its logical reps are canonical phase-0 all-X / all-Z, satisfying every typed
  hypothesis trivially, and `native_decide` closes its n=49 check-matrix field.

## The construction

### Qubit index model

Physical qubit `q : Fin (n₁·n₂)` decomposes as block `b = q / n₁ : Fin n₂`
and position `i = q % n₁ : Fin n₁`, with `qIdx b i = b·n₁ + i`. `[NeZero n₁]`
makes `blockOf`/`posOf` well-defined. (Mirrors the toric row-major indexing
`rowMajor_injective` in `Geometry/GridIndexing.lean`.)

### Generators of the concatenated code

Two families, total `n₂·(n₁−1) + (n₂−k₂) = n₁·n₂ − k₂ = n − k` generators:

1. **Inner stabilizers, replicated per block.** For each block `b : Fin n₂`
   and each inner generator `g` (there are `n₁ − 1` of them, k₁=1): embed `g`
   into block `b`, identity on all other blocks. `n₂·(n₁−1)` generators.

2. **Promoted outer stabilizers.** For each outer generator `h` (there are
   `n₂ − k₂`), replace each single-qubit Pauli on outer-qubit `b` by the inner
   logical on block `b` via the promotion map
   `I ↦ I`, `X ↦ X̄₁`, `Z ↦ Z̄₁` (CSS: no `Y`). `n₂ − k₂` generators.

### Why the promoted generators commute *on the nose*

Promotion is a homomorphism only *modulo the inner stabilizer* (logical reps
`X̄₁² ∈ stabilizer`, not `= I`), yet the concatenated generators commute
**exactly** — required by `StabilizerGroup`. Reason: commutation = parity of
the number of qubit positions where two Paulis anticommute
(`commutes_iff_even_anticommutes`, `Commutation.lean:142`). Promotion
preserves the per-block anticommutation pattern, so the total anticommuting-
position count of two promoted outer generators has the **same parity** as the
anticommuting-qubit count of the two underlying outer generators — which is
even because the outer generators commute. This parity argument is the heart
of the constructor and is well-supported by the existing repo lemma.

### Logical operators of the concatenated code

The concatenated logicals are the *promoted outer logicals*: for `ℓ : Fin k₂`,
`X̄ᶜ_ℓ = promote (X̄₂_ℓ)`, `Z̄ᶜ_ℓ = promote (Z̄₂_ℓ)`. Their anticommutation
descends from `(Cout.logicalOps ℓ).anticommute`; centralizer membership from
the parity argument.

## Theorems to formalize

Organized by the 7-milestone plan (see `plan.md` for full signatures, LOC,
and dependency graph). Proposed names, design-level:

### Tier 0 — embedding calculus (M1)
- `embedBlock (b) (g)` and operator-level `mulOp_embedBlockOp_operators`
- `weight_embedBlock : (embedBlock b g).weight = g.weight`
- `weight_ge_of_blocks_ge` — weight superadditivity over disjoint blocks
- `embedBlock_commute_iff`, `embedBlock_anticommute_iff` (parity route only),
  `embedBlock_cross_commute` (different blocks always commute)

### Tier 1a — promotion + typing (M2)
- `ConcatCSSData` bundle (carries the typed inner/outer sublists and the
  CSS-typed, phase-0 inner logical reps as explicit hypotheses)
- `promoteE`, `promoteSingle_noY_of_isXType/isZType` (Y-branch provably dead),
  `promoteE_isX/isZ`
- `concatGeneratorsList`, `concatGeneratorsList_length` (`= n₁·n₂ − k₂`),
  `concatGeneratorsList_phaseZero`

### Tier 1b — constructor (M3)
- `promote_anticommute_filter_card_parity` (build & verify first, in isolation)
- `concat_generators_commute`, `concat_closure_no_neg_identity`
- `rowsLinearIndependent_concat` (or a `ConcatCSSData` field, per-instance)
- `concatLogicalX/Z`, their centralizer membership and anticommutation
- `concatenate : ConcatCSSData n₁ n₂ k₂ → StabilizerCode (n₁·n₂) k₂`

### Tier 1.5 — inner centralizer classification (M4, the long pole)
- `mem_stabilizer_of_commutes_both_logicals`
- `centralizer_classify_of_k1 : g ∈ centralizer → g ∈ stabilizer ∨ IsNontrivialLogicalOperator g`
  (proved via the existing symplectic span bridge; the inner centralizer is
  `stabilizer ⊔ ⟨X̄₁, Z̄₁⟩`, dimension-2 quotient for k=1)

### Tier 2a — restriction + correspondence (M5)
- `restrictBlock`, `weight_eq_sum_restrictBlock`, `restrictBlock_mem_centralizer`
- `inducedOuter`, `inducedOuter_support_eq` (uses M4),
  `inducedOuter_mem_centralizer`, `inducedOuter_not_mem_stabilizer` (uses M4),
  `inducedOuter_isNontrivialLogical`

### Tier 2b — distance (M6, the headline)
- `weight_ge_d1_mul_d2`
- `concatWitness`, `concatWitness_weight (= d₁·d₂)`, `concatWitness_isNontrivialLogical`
- `concat_hasCodeDistance : HasCodeDistance (concatenate D) (d₁·d₂)`

### Instance (M7)
- `steaneConcatData : ConcatCSSData 7 7 1`, `steaneConcat : StabilizerCode 49 1`
- `steaneConcat_distance : HasCodeDistance steaneConcat 9`

## The distance argument (informal)

Let `L` be any nontrivial logical of `concatenate D`. `L ∈ centralizer` ⇒ it
commutes with every inner stabilizer ⇒ (by `centralizer_classify_of_k1`, M4)
the restriction `restrictBlock b L` to each block is either an inner stabilizer
or a **nontrivial inner logical** (weight ≥ `d₁`). The blocks carrying a
nontrivial inner logical form the support of the **induced outer operator**
`inducedOuter D L`, which is a **nontrivial outer logical** (M5) ⇒ its outer
weight ≥ `d₂`, i.e. ≥ `d₂` blocks each contribute weight ≥ `d₁`. Weight
superadditivity over disjoint blocks (`weight_ge_of_blocks_ge`, M1) gives
`weight L ≥ d₁·d₂`. The matching witness `concatWitness` (promote of a minimum-
weight outer `X̄₂` with each block carrying minimum-weight `X̄₁`) has weight
exactly `d₁·d₂`.

**Why no brute force:** the `HasCodeDistance` witness quantifies over all
nontrivial logicals, i.e. ~`4^n` Paulis. At n=49 that is ~`3×10²⁹` — the
structural proof above is mandatory, not a convenience.

## Edge cases / convention notes

1. **Zero-phase convention everywhere.** `embedBlock`/`promoteE` are
   `ofOperator (… )` so `phasePower = 0` definitionally. This is required for
   `generators_phaseZero` and avoids an unsound group-level "embedding is a
   homomorphism" claim (see `gap_audit.md`, R2).
2. **Promotion over typed sublists only.** Promote over `outerZ ++ outerX`
   (CSS-typed), never the raw `Cout.generatorsList`, so the `Y ↦ I` branch is
   provably unreachable (R3).
3. **Restrictions may be Y-class.** `restrictBlock b L` can carry the `X̄₁Z̄₁`
   (Y) class on a block; CSS-typing it is unsound. Use the phase/Y-agnostic
   operator-part lemmas instead (R4).
4. **k₁ = 1 excluded otherwise.** k₁ ≥ 2 changes the induced-outer object from
   a single Pauli class per block to a tuple; out of scope.

## Relation to existing repo files

| Existing file | Relationship |
|---|---|
| `Codes/Small/Shor9.lean` | Shor is itself a concatenation (3-bit phase ∘ 3-bit flip); conceptual precedent |
| `Codes/Small/Steane7.lean` | source of the M7 inner/outer instance (phase-0 all-X/all-Z reps) |
| `Codes/Iceberg/N.lean` | parametric CSS packaging template (`Fact`-style constraint, `Fin k` logicals) |
| `Codes/Toric/Distance*.lean` | structural template for a parametric distance proof (file split, min-weight argument) |
| `Framework/Symplectic/SymplecticSpan.lean` | the span↔subgroup bridge that makes M4 reuse, not author |
| `Framework/Core/Logical/LogicalOperators.lean` | phase/Y-agnostic operator-part lemmas; `LogicalQubitOps` target |
| `Framework/Core/CSS/CSSPredicates.lean` | `IsXTypeElement`/`IsZTypeElement` for typed promotion |
| `Codes/_TEMPLATE.lean` | canonical §1–§14 structure for the constructor file |

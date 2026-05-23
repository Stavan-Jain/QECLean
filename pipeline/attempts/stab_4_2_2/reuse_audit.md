# Reuse audit: [[4,2,2]] Four-qubit code

## Directly applicable (use as-is)

- `NQubitPauliGroupElement n` and its `mul`, `Anticommute`, `weight`, `support`
  — `QEC/Stabilizer/Foundations/PauliGroup/NQubitElement.lean`.
- `NQubitPauliOperator.identity`, `.set`, `.X`, `.Z`, `.weight` — same place.
- `PauliOperator.IsZType`, `IsXType`, `mulOp` —
  `QEC/Stabilizer/Foundations/PauliGroup/SingleQubit/*` (Pauli single-qubit).
- `NQubitPauliGroupElement.IsZTypeElement`, `IsXTypeElement` —
  `QEC/Stabilizer/Framework/Core/CSS/CSSPredicates.lean`.
- `StabilizerGroup`, `.toSubgroup`, `negIdentity` —
  `QEC/Stabilizer/Framework/Core/Stabilizer/StabilizerGroup.lean`.
- `StabilizerCode n k` structure and its fields/accessors —
  `QEC/Stabilizer/Framework/Core/Stabilizer/StabilizerCode.lean`.
- `LogicalQubitOps`, `.xOp_nontrivial`, `.zOp_nontrivial`,
  `.xOp_IsPauliLogicalOperator` — `QEC/Stabilizer/Framework/Core/Logical/LogicalOperators.lean`.
- `IsNontrivialLogicalOperator`, `IsNontrivialLogicalOperator_iff` —
  same file.
- `HasCodeDistance`, `hasCodeDistance_of`, `HasCodeDistance.min_weight` —
  `QEC/Stabilizer/Framework/Core/Logical/CodeDistance.lean`.
- `centralizer`, `mem_centralizer_iff`, `mem_centralizer_iff_closure` —
  `QEC/Stabilizer/Framework/Core/Stabilizer/Centralizer.lean`.
- `CSS.negIdentity_not_mem_closure_union` —
  `QEC/Stabilizer/Framework/Core/CSS/CSSNoNegI.lean`. **Direct fit for T5** since our
  generator set is a union of one Z-type and one X-type generator.
- `CSSCommutationLemmas.ZType_commutes`, `XType_commutes` —
  `QEC/Stabilizer/Framework/Core/CSS/CSSCommutationLemmas.lean`. **Direct fit for T4** to
  combine T1 + T2 + T3 into the full pairwise-commute conclusion.
- `NQubitPauliGroupElement.AllPhaseZero`, `AllPhaseZero_cons`,
  `AllPhaseZero_nil` — same file as `NQubitElement`.
- `NQubitPauliGroupElement.rowsLinearIndependent`,
  `rowsLinearIndependent_implies_independentGenerators`,
  `GeneratorsIndependent_of_rowsLinearIndependent` —
  `QEC/Stabilizer/Framework/Symplectic/IndependentEquiv.lean`.
- `NQubitPauliGroupElement.listToSet`, `listToSet_cons`, `listToSet_nil` —
  `QEC/Stabilizer/Foundations/PauliGroup/NQubitElement.lean`.
- `mkStabilizerFromGenerators` — `QEC/Stabilizer/Framework/Core/Stabilizer/StabilizerCode.lean`.
- `pauli_comm_even_anticommutes`, `pauli_comm_componentwise` (tactics) —
  `QEC/Stabilizer/Foundations/PauliGroup/CommutationTactics.lean`.
- `NQubitPauliGroupElement.anticommutesAt`,
  `commutes_iff_even_anticommutes` —
  `QEC/Stabilizer/Foundations/PauliGroup/Commutation.lean`.
- `anticommutes_imp_not_isPauliLogicalOperator`,
  `isPauliLogicalOperator_iff_mem_centralizer` —
  `QEC/Stabilizer/Framework/Core/Logical/LogicalOperators.lean`. **Needed for T13** to rule
  out weight-1 logicals.

## Lightly adapted (existing pattern, new instance)

- **`generatorsList` + `listToSet_generatorsList` lemma**: from `Steane7.lean:286`
  and `:290`. Two-element list this time (`[Z1, X1]`) instead of six.
- **`stabilizerGroup_toSubgroup_eq` lemma**: from `Steane7.lean:307`. One-line.
- **`AllPhaseZero_generatorsList`**: pattern from `Steane7.lean:320`. Two
  `cons` cases only.
- **`rowsLinearIndependent_generatorsList`**: from `Steane7.lean:330`. Same
  `by decide` closer.
- **`GeneratorsIndependent_7_generatorsList`** → renamed
  `GeneratorsIndependent_4_generatorsList`. From `Steane7.lean:334`.
- **`logicalX_mem_centralizer` template**: from `Steane7.lean:413`. Adapted
  to four logicals (X̄₁, X̄₂, Z̄₁, Z̄₂) and only two generators each.
- **Direct CSS pattern (Z-only + X-only generators, one each)**: this code's
  structure is similar in spirit to a "degenerate Steane7" — a CSS code with
  the same row pattern on both Z and X sides (here both rows are all-ones).
  The Steane7 proofs translate over directly, just smaller.

## New per-code definitions (no analog in repo)

- **k = 2 logical operators**: `logicalX_1`, `logicalX_2`, `logicalZ_1`,
  `logicalZ_2` as concrete Pauli strings (IXIX, IIXX, IIZZ, IZIZ). Every
  existing repo code has either k = 1 (Steane7, Shor9, RepetitionCode*,
  RotatedSurfaceCode3) or k = 1 with parametric n (RotatedSurfaceCodeN,
  ToricCodeN). The [[4,2,2]] is the first concrete k = 2 instance.
- **Off-diagonal logical commutation lemmas**:
  - `logicalX_1_commutes_logicalX_2`
  - `logicalX_1_commutes_logicalZ_2`
  - `logicalZ_1_commutes_logicalX_2`
  - `logicalZ_1_commutes_logicalZ_2`

  These have no direct analog in Steane7 / Shor9 (where Subsingleton.elim
  short-circuits the cross-commutation field).
- **`logicalOps` as a `Fin 2`-indexed family**: trivial in shape, but the
  first non-vacuous instance.
- **Distance-2 finite enumeration for d = 2**: this is the smallest
  non-trivial distance in the repo. RepetitionCode3 has d = 1 (trivially
  closed by `Nat.one_le_of_lt hw_pos`), and all other distance proofs are
  d ≥ 3 (Steane has d = 3; surface/toric codes have parametric d ≥ 3). The
  d = 2 proof has to actively enumerate weight-1 errors and show each
  anticommutes with a stabilizer — a slightly different shape than the
  existing distance proofs.

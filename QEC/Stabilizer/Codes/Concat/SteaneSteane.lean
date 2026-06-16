import QEC.Stabilizer.Framework.Concatenation
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Steane7Distance

/-!
# Steane ⊗ Steane: the concatenated `[[49, 1, ≥ 9]]` instance (Milestone M7)

The validating concrete instance of the CSS concatenation framework
(`pipeline/attempts/concat_css_general/plan.md`): concatenate the Steane `[[7,1,3]]` code with
itself. `steaneConcatData` bundles `Steane7.stabilizerCode` as both inner and outer code into a
`ConcatCSSData 7 7 1` — the data the whole framework consumes.

## Status and the two instantiation blockers

`steaneConcatData` typechecks (below), so the framework's input bundle instantiates on a real
code. The inner/outer distance `HasCodeDistance Steane7.stabilizerCode 3`
(`Steane7.stabilizerCode_hasCodeDistance_three`) is now formalized, so
`steaneConcat_hasCodeDistance_nine` reduces the `[[49, 1, 9]]` distance to exactly **two
remaining inputs**, the generator
independence and a weight-9 witness:

* **Generator independence is not `native_decide`-able.** `concatenate` requires
  `GeneratorsIndependent 49 concatGeneratorsList`. The only available decision procedure,
  `Decidable (rowsLinearIndependent L)` (`CheckMatrixDecidable.lean`), enumerates *all*
  `2 ^ L.length` coefficient vectors. The concatenated list has `49 − 1 = 48` generators, so
  that is `2⁴⁸` — infeasible (OOM). The plan's "`native_decide` per instance" fallback (risk
  R5) works only for small single codes (Steane itself: `2⁶`); it does **not** scale. The real
  fix is a *structural* `rowsLinearIndependent_concat` lemma deriving concat-independence from
  the inner/outer independence and the disjoint block-support of the embedded inner generators —
  a new framework lemma (≈ M4-scale), not a decision.

* **A weight-9 witness** — a nontrivial concatenated logical of weight exactly `9`. (The fixed
  `concatLogicalX` has weight `≥ 9` but a minimum-weight representative is the witness; it too
  routes through the noncomputable concatenated stabilizer, so it needs the same computable
  restatement the independence does.)

Both are recorded in `pipeline/attempts/concat_css_general/state.yaml`. The abstract framework
(M1–M6) is complete and sorry-free; `steaneConcat_hasCodeDistance_nine` is the honest end state
for M7 with the current infrastructure.
-/

namespace Quantum.StabilizerGroup.Steane7

open Quantum.Concatenation NQubitPauliGroupElement

/-- The Steane ⊗ Steane concatenation data: `Steane7.stabilizerCode` as both inner and outer
code, with the CSS `Z`/`X` generator split `[Z1,Z2,Z3] ++ [X1,X2,X3]` and the all-`X` / all-`Z`
phase-0 logicals. This is the `ConcatCSSData` bundle the whole framework consumes; it typechecks,
validating that the framework's input shape instantiates on the Steane code. -/
noncomputable def steaneConcatData : ConcatCSSData 7 7 1 where
  Cin := stabilizerCode
  Cout := stabilizerCode
  innerZ := [Z1, Z2, Z3]
  innerX := [X1, X2, X3]
  inner_split := List.Perm.refl _
  innerZ_isZ := fun g hg => ZGenerators_are_ZType g (by simpa [ZGenerators] using hg)
  innerX_isX := fun g hg => XGenerators_are_XType g (by simpa [XGenerators] using hg)
  outerZ := [Z1, Z2, Z3]
  outerX := [X1, X2, X3]
  outer_split := List.Perm.refl _
  outerZ_isZ := fun g hg => ZGenerators_are_ZType g (by simpa [ZGenerators] using hg)
  outerX_isX := fun g hg => XGenerators_are_XType g (by simpa [XGenerators] using hg)
  innerLogX_isX := fun _ => Or.inr rfl
  innerLogX_phaseZero := rfl
  innerLogZ_isZ := fun _ => Or.inr rfl
  innerLogZ_phaseZero := rfl
  outerLogX_isX := fun _ _ => Or.inr rfl
  outerLogZ_isZ := fun _ _ => Or.inr rfl

open Quantum.StabilizerGroup

/-- **(M7, conditional headline.)** Steane ⊗ Steane has distance `9 = 3 · 3`, *given* the two
remaining concrete inputs: the concatenated generator independence `hindep` and a weight-9
nontrivial-logical witness `hwit`. The inner/outer distance-3 is supplied by
`stabilizerCode_hasCodeDistance_three`; everything else is M6's `concat_hasCodeDistance`.

This pins down exactly what an unconditional `[[49, 1, 9]]` proof still needs (see the module
doc): a structural concat-independence lemma and a computable minimum-weight witness. -/
theorem steaneConcat_hasCodeDistance_nine
    (hindep : GeneratorsIndependent (7 * 7) steaneConcatData.concatGeneratorsList)
    (hwit : ∃ g, IsNontrivialLogicalOperator g steaneConcatData.concatStabGroup
      ∧ NQubitPauliGroupElement.weight g = 3 * 3) :
    HasCodeDistance (steaneConcatData.concatenate hindep) 9 :=
  steaneConcatData.concat_hasCodeDistance hindep rowsLinearIndependent_generatorsList
    stabilizerCode_hasCodeDistance_three stabilizerCode_hasCodeDistance_three hwit

end Quantum.StabilizerGroup.Steane7

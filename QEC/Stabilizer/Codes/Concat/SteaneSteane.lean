import QEC.Stabilizer.Framework.Concatenation
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Steane7Distance

/-!
# Steane ⊗ Steane: the concatenated `[[49, 1, ≥ 9]]` instance (Milestone M7)

The validating concrete instance of the CSS concatenation framework
(`pipeline/attempts/concat_css_general/plan.md`): concatenate the Steane `[[7,1,3]]` code with
itself. `steaneConcatData` bundles `Steane7.stabilizerCode` as both inner and outer code into a
`ConcatCSSData 7 7 1` — the data the whole framework consumes.

## Status

`steaneConcatData` typechecks (below), so the framework's input bundle instantiates on a real
code. The inner/outer distance `HasCodeDistance Steane7.stabilizerCode 3`
(`Steane7.stabilizerCode_hasCodeDistance_three`) is formalized, and the **generator independence
is now discharged** (`steaneConcat_generatorsIndependent`) via the structural framework lemma
`ConcatCSSData.generatorsIndependent_concat` (`Concatenation/Independence.lean`): it derives the
`2⁴⁸`-infeasible `GeneratorsIndependent 49 concatGeneratorsList` from two *small*,
`native_decide`-able inputs —

* the Steane generators together with the two logical representatives are symplectically
  independent (`rowsLinearIndependent (generatorsList ++ [logicalX, logicalZ])`, `2⁸`), and
* the outer Steane generators are symplectically independent (`2⁶`).

So `steaneConcat_hasCodeDistance_nine` now reduces the `[[49, 1, 9]]` distance to exactly **one
remaining input**:

* **A weight-9 witness** — a nontrivial concatenated logical of weight exactly `9`. (The fixed
  `concatLogicalX` has weight `≥ 9` but a minimum-weight representative is the witness; it
  routes through the noncomputable concatenated stabilizer, so it needs a computable
  restatement.)

Recorded in `pipeline/attempts/concat_css_general/state.yaml`. The abstract framework (M1–M6) is
complete and sorry-free.
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

/-- **(M7.)** The concatenated generators are independent — `GeneratorsIndependent 49`,
discharging the hypothesis `concatenate` takes. Proven via the structural framework lemma
`ConcatCSSData.generatorsIndependent_concat`, whose two inputs are small enough to settle by
`native_decide` (`2⁸` for the inner-with-logicals list, `2⁶` for the outer), sidestepping the
`2⁴⁸` direct check on the 48 concatenated generators. -/
theorem steaneConcat_generatorsIndependent :
    GeneratorsIndependent (7 * 7) steaneConcatData.concatGeneratorsList := by
  have hin : NQubitPauliGroupElement.rowsLinearIndependent
      (generatorsList ++ [logicalX, logicalZ]) := by native_decide
  have hout : NQubitPauliGroupElement.rowsLinearIndependent
      ([Z1, Z2, Z3] ++ [X1, X2, X3]) := by native_decide
  exact steaneConcatData.generatorsIndependent_concat hin hout

/-- **(M7, conditional headline.)** Steane ⊗ Steane has distance `9 = 3 · 3`, *given* the one
remaining concrete input: a weight-9 nontrivial-logical witness `hwit`. The generator
independence is now supplied by `steaneConcat_generatorsIndependent`, the inner/outer distance-3
by `stabilizerCode_hasCodeDistance_three`; everything else is M6's `concat_hasCodeDistance`.

This pins down exactly what an unconditional `[[49, 1, 9]]` proof still needs (see the module
doc): a computable minimum-weight witness. -/
theorem steaneConcat_hasCodeDistance_nine
    (hwit : ∃ g, IsNontrivialLogicalOperator g steaneConcatData.concatStabGroup
      ∧ NQubitPauliGroupElement.weight g = 3 * 3) :
    HasCodeDistance (steaneConcatData.concatenate steaneConcat_generatorsIndependent) 9 :=
  steaneConcatData.concat_hasCodeDistance steaneConcat_generatorsIndependent
    rowsLinearIndependent_generatorsList
    stabilizerCode_hasCodeDistance_three stabilizerCode_hasCodeDistance_three hwit

end Quantum.StabilizerGroup.Steane7

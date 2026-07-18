import QEC.Stabilizer.Framework.Concatenation
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Steane7Distance

/-!
# Steane ⊗ Steane: the concatenated `[[49, 1, 9]]` instance (Milestone M7)

The validating concrete instance of the CSS concatenation framework
(`qec-lab:pipeline/attempts/concat_css_general/plan.md`): concatenate the Steane `[[7,1,3]]` code with
itself. `steaneConcatData` bundles `Steane7.stabilizerCode` as both inner and outer code into a
`ConcatCSSData 7 7 1` — the data the whole framework consumes.

## Status: COMPLETE — `steaneConcat_hasCodeDistance_nine` is unconditional

`HasCodeDistance (steaneConcatData.concatenate …) 9` holds with **no hypotheses**. Every input
of M6's `concat_hasCodeDistance` is discharged:

* **inner/outer distance-3** — `Steane7.stabilizerCode_hasCodeDistance_three`;
* **generator independence** (`steaneConcat_generatorsIndependent`) — the structural framework
  lemma `ConcatCSSData.generatorsIndependent_concat` (`Concatenation/Independence.lean`) reduces
  the `2⁴⁸`-infeasible `GeneratorsIndependent 49 concatGeneratorsList` to two *small*,
  `native_decide`-able inputs: `rowsLinearIndependent (generatorsList ++ [logicalX, logicalZ])`
  (`2⁸`) and the outer Steane generators (`2⁶`);
* **weight-9 witness** (`steaneConcat_witness`) — an explicit nontrivial concatenated logical of
  weight exactly `9 = 3·3`: the inner weight-3 logical `X` (on `{3,5,6}`) placed on the three
  active outer blocks `{3,5,6}`. Centralizer membership and the anticommuting partner (all-`Z`)
  are settled by `native_decide` on the concrete generator list (`concatGensConcrete`, `rfl`-equal
  to `steaneConcatData.concatGeneratorsList`).

Recorded in `qec-lab:pipeline/attempts/concat_css_general/state.yaml`. The abstract framework (M1–M6) is
sorry-free; the only trust beyond the kernel is `native_decide`'s compiler trust on the small
concrete enumerations.
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

open NQubitPauliOperator

/-! ## The weight-9 minimum-weight witness

The remaining `concat_hasCodeDistance` input: an explicit nontrivial concatenated logical of
weight exactly `9 = 3 · 3`. It is the inner weight-3 logical `X` (on `{3,5,6}`) placed on the
three active outer blocks `{3,5,6}` — `X` on 9 physical qubits. Centralizer membership and the
anticommuting partner (all-`Z`) are settled by `native_decide` on the *concrete* generator list
(`rfl`-equal to `steaneConcatData.concatGeneratorsList`, whose `stabilizerCode` projections are
not themselves native-computable). -/

/-- Concrete form of `steaneConcatData.concatGeneratorsList` — the `stabilizerCode` projections
reduced to the explicit Steane generators / logicals, so the commutation checks below settle by
`native_decide`. `rfl`-equal to the original. -/
private def concatGensConcrete : List (NQubitPauliGroupElement (7 * 7)) :=
  (List.finRange 7).flatMap (fun b => generatorsList.map (embedBlock b))
    ++ ([Z1, Z2, Z3] ++ [X1, X2, X3]).map (promoteE logicalX.operators logicalZ.operators)

/-- The weight-9 logical operator: inner logical `X` on `{3,5,6}` of the three active outer
blocks `{3,5,6}`. -/
private def witnessOp : NQubitPauliOperator (7 * 7) := fun q =>
  if (Quantum.Concatenation.blockOf q = 3 ∨ Quantum.Concatenation.blockOf q = 5
        ∨ Quantum.Concatenation.blockOf q = 6)
      ∧ (Quantum.Concatenation.posOf q = 3 ∨ Quantum.Concatenation.posOf q = 5
        ∨ Quantum.Concatenation.posOf q = 6)
  then PauliOperator.X else PauliOperator.I

private def witnessE : NQubitPauliGroupElement (7 * 7) := ⟨0, witnessOp⟩

/-- The all-`Z` element: a centralizer member anticommuting with the witness (used to certify
nontriviality). -/
private def allZ : NQubitPauliGroupElement (7 * 7) := ⟨0, NQubitPauliOperator.Z (7 * 7)⟩

private lemma witnessE_weight : witnessE.weight = 3 * 3 := by native_decide

private lemma witness_comm :
    ∀ s ∈ concatGensConcrete, symplecticInner s.operators witnessOp = 0 := by native_decide

private lemma allZ_comm :
    ∀ s ∈ concatGensConcrete, symplecticInner s.operators (NQubitPauliOperator.Z (7 * 7)) = 0 := by
  native_decide

private lemma witness_anti_allZ_symp :
    symplecticInner witnessOp (NQubitPauliOperator.Z (7 * 7)) = 1 := by native_decide

/-- Anticommutation depends only on operator parts. -/
private lemma anticommute_of_operators_eq {m : ℕ} (p q r : NQubitPauliGroupElement m)
    (h : p.operators = q.operators) (h_ac : NQubitPauliGroupElement.Anticommute p r) :
    NQubitPauliGroupElement.Anticommute q r := by
  rw [NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes] at h_ac ⊢
  classical
  have : Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt q.operators r.operators) =
      Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt p.operators r.operators) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [h]
  rw [this]; exact h_ac

private lemma allZ_mem_centralizer : allZ ∈ centralizer steaneConcatData.concatStabGroup :=
  CentralizerLemmas.mem_centralizer_of_commutes_list allZ steaneConcatData.concatStabGroup
    concatGensConcrete rfl
    (fun s hs =>
      (NQubitPauliOperator.commutes_iff_symplectic_inner_zero s allZ).mpr (allZ_comm s hs))

private lemma witnessE_mem_centralizer :
    witnessE ∈ centralizer steaneConcatData.concatStabGroup :=
  CentralizerLemmas.mem_centralizer_of_commutes_list witnessE steaneConcatData.concatStabGroup
    concatGensConcrete rfl
    (fun s hs =>
      (NQubitPauliOperator.commutes_iff_symplectic_inner_zero s witnessE).mpr (witness_comm s hs))

private lemma witness_anti_allZ : NQubitPauliGroupElement.Anticommute witnessE allZ :=
  (NQubitPauliOperator.anticommutes_iff_symplectic_inner_one witnessE allZ).mpr
    witness_anti_allZ_symp

/-- The explicit weight-9 nontrivial concatenated logical, discharging the final
`concat_hasCodeDistance` input. -/
private lemma steaneConcat_witness :
    ∃ g, IsNontrivialLogicalOperator g steaneConcatData.concatStabGroup
      ∧ NQubitPauliGroupElement.weight g = 3 * 3 := by
  refine ⟨witnessE, (IsNontrivialLogicalOperator_iff _ _).mpr ⟨witnessE_mem_centralizer, ?_, ?_⟩,
    witnessE_weight⟩
  · exact not_mem_stabilizer_of_anticommutes_centralizer steaneConcatData.concatStabGroup
      witnessE allZ allZ_mem_centralizer witness_anti_allZ
  · intro s hs h_ops
    exact absurd hs (not_mem_stabilizer_of_anticommutes_centralizer
      steaneConcatData.concatStabGroup s allZ allZ_mem_centralizer
      (anticommute_of_operators_eq witnessE s allZ h_ops.symm witness_anti_allZ))

/-- **(M7 headline, unconditional.)** Steane ⊗ Steane is a `[[49, 1, 9]]` code: distance
`9 = 3 · 3`. All inputs are now discharged — generator independence by
`steaneConcat_generatorsIndependent` (structural lemma + `native_decide`), the inner/outer
distance-3 by `stabilizerCode_hasCodeDistance_three`, and the weight-9 witness by
`steaneConcat_witness`. -/
theorem steaneConcat_hasCodeDistance_nine :
    HasCodeDistance (steaneConcatData.concatenate steaneConcat_generatorsIndependent) 9 :=
  steaneConcatData.concat_hasCodeDistance steaneConcat_generatorsIndependent
    rowsLinearIndependent_generatorsList
    stabilizerCode_hasCodeDistance_three stabilizerCode_hasCodeDistance_three steaneConcat_witness

/-- **The Steane ⊗ Steane `[[49, 1, 9]]` code as a first-class `StabilizerCodeWithDistance`** —
all three parameters in its type, via the framework bundler `concatenateWithDistance`. -/
noncomputable def steaneConcatCodeWithDistance : StabilizerCodeWithDistance 49 1 9 :=
  steaneConcatData.concatenateWithDistance steaneConcat_generatorsIndependent
    rowsLinearIndependent_generatorsList
    stabilizerCode_hasCodeDistance_three stabilizerCode_hasCodeDistance_three steaneConcat_witness

end Quantum.StabilizerGroup.Steane7

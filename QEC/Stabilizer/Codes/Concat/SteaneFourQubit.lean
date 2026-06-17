import QEC.Stabilizer.Framework.Concatenation
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Steane7Distance
import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2

/-!
# Steane ⊗ [[4,2,2]]: the concatenated `[[28, 2, 6]]` instance (k₂ > 1)

A second validating instance of the CSS concatenation framework, chosen to exercise the
**multi-logical-qubit** (`k₂ > 1`) path that the Steane ⊗ Steane instance (`k₂ = 1`,
`SteaneSteane.lean`) does not: concatenate the Steane `[[7,1,3]]` inner code with the
`[[4,2,2]]` outer code (`k₂ = 2`). `steane422Data` bundles them into a `ConcatCSSData 7 4 2`.

The headline `steane422_hasCodeDistance_six : HasCodeDistance (steane422Data.concatenate …) 6`
is **unconditional** — every `concat_hasCodeDistance` input is discharged exactly as for
Steane ⊗ Steane, reusing the same framework lemmas:

* inner distance-3 `Steane7.stabilizerCode_hasCodeDistance_three` and outer distance-2
  `FourQubit_4_2_2.code_has_distance_two`;
* generator independence `steane422_generatorsIndependent`, from the structural
  `ConcatCSSData.generatorsIndependent_concat` + `native_decide` on the two small inputs
  (Steane `2⁸`, `[[4,2,2]]` `2²`);
* a weight-`6 = 3·2` witness `steane422_witness`: the inner weight-3 logical `X` (on `{3,5,6}`)
  on the two blocks `{1,3}` of the outer logical `X̄₁ = IXIX`.

This shows the framework — already parametric in `k₂` — works on `k₂ = 2` end to end.
-/

namespace Quantum.StabilizerGroup.Steane7

open Quantum.Concatenation NQubitPauliGroupElement

/-- Steane ⊗ [[4,2,2]] concatenation data: Steane `[[7,1,3]]` inner, `[[4,2,2]]` outer (`k₂ = 2`).
The inner fields are exactly those of `steaneConcatData`; the outer fields come from
`FourQubit_4_2_2` (generators `[Z1, X1]`, the two-qubit logical family). -/
noncomputable def steane422Data : ConcatCSSData 7 4 2 where
  Cin := stabilizerCode
  Cout := FourQubit_4_2_2.stabilizerCode
  innerZ := [Z1, Z2, Z3]
  innerX := [X1, X2, X3]
  inner_split := List.Perm.refl _
  innerZ_isZ := fun g hg => ZGenerators_are_ZType g (by simpa [ZGenerators] using hg)
  innerX_isX := fun g hg => XGenerators_are_XType g (by simpa [XGenerators] using hg)
  outerZ := [FourQubit_4_2_2.Z1]
  outerX := [FourQubit_4_2_2.X1]
  outer_split := List.Perm.refl _
  outerZ_isZ := fun g hg =>
    FourQubit_4_2_2.ZGenerators_are_ZType g (by simpa [FourQubit_4_2_2.ZGenerators] using hg)
  outerX_isX := fun g hg =>
    FourQubit_4_2_2.XGenerators_are_XType g (by simpa [FourQubit_4_2_2.XGenerators] using hg)
  innerLogX_isX := fun _ => Or.inr rfl
  innerLogX_phaseZero := rfl
  innerLogZ_isZ := fun _ => Or.inr rfl
  innerLogZ_phaseZero := rfl
  outerLogX_isX := fun ℓ => by
    fin_cases ℓ <;> (unfold NQubitPauliOperator.IsXType PauliOperator.IsXType; decide)
  outerLogZ_isZ := fun ℓ => by
    fin_cases ℓ <;> (unfold NQubitPauliOperator.IsZType PauliOperator.IsZType; decide)

open Quantum.StabilizerGroup NQubitPauliOperator

/-! ## Generator independence -/

/-- The concatenated generators are independent — discharged by the structural framework lemma
`generatorsIndependent_concat`, whose two inputs are small (`2⁸` inner-with-logicals, `2²`
outer) and settled by `native_decide`. -/
theorem steane422_generatorsIndependent :
    GeneratorsIndependent (7 * 4) steane422Data.concatGeneratorsList := by
  have hin : NQubitPauliGroupElement.rowsLinearIndependent
      (generatorsList ++ [logicalX, logicalZ]) := by native_decide
  have hout : NQubitPauliGroupElement.rowsLinearIndependent
      ([FourQubit_4_2_2.Z1] ++ [FourQubit_4_2_2.X1]) := by native_decide
  exact steane422Data.generatorsIndependent_concat hin hout

/-! ## The weight-6 minimum-weight witness -/

/-- Concrete form of `steane422Data.concatGeneratorsList`, `rfl`-equal to it, so the witness's
commutation checks settle by `native_decide` (the `stabilizerCode` projections are not
native-computable, but reduce by `rfl`). -/
private def concatGens422 : List (NQubitPauliGroupElement (7 * 4)) :=
  (List.finRange 4).flatMap (fun b => generatorsList.map (embedBlock b))
    ++ ([FourQubit_4_2_2.Z1] ++ [FourQubit_4_2_2.X1]).map
        (promoteE logicalX.operators logicalZ.operators)

/-- The weight-6 logical: inner logical `X` on `{3,5,6}` of the two blocks `{1,3}` — the support
of the outer logical `X̄₁ = IXIX`. -/
private def witnessOp422 : NQubitPauliOperator (7 * 4) := fun q =>
  if (Quantum.Concatenation.blockOf q = 1 ∨ Quantum.Concatenation.blockOf q = 3)
      ∧ (Quantum.Concatenation.posOf q = 3 ∨ Quantum.Concatenation.posOf q = 5
        ∨ Quantum.Concatenation.posOf q = 6)
  then PauliOperator.X else PauliOperator.I

private def witnessE422 : NQubitPauliGroupElement (7 * 4) := ⟨0, witnessOp422⟩

/-- The anticommuting centralizer partner: `Z` on the two blocks `{2,3}` — the support of the
outer logical `Z̄₁ = IIZZ`. It overlaps the witness in `3` (odd) qubits, so they anticommute. -/
private def zOp422 : NQubitPauliOperator (7 * 4) := fun q =>
  if Quantum.Concatenation.blockOf q = 2 ∨ Quantum.Concatenation.blockOf q = 3
  then PauliOperator.Z else PauliOperator.I

private def zE422 : NQubitPauliGroupElement (7 * 4) := ⟨0, zOp422⟩

private lemma witnessE422_weight : witnessE422.weight = 3 * 2 := by native_decide

private lemma witness422_comm :
    ∀ s ∈ concatGens422, symplecticInner s.operators witnessOp422 = 0 := by native_decide

private lemma z422_comm :
    ∀ s ∈ concatGens422, symplecticInner s.operators zOp422 = 0 := by native_decide

private lemma witness422_anti_z422_symp : symplecticInner witnessOp422 zOp422 = 1 := by
  native_decide

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

private lemma zE422_mem_centralizer : zE422 ∈ centralizer steane422Data.concatStabGroup :=
  CentralizerLemmas.mem_centralizer_of_commutes_list zE422 steane422Data.concatStabGroup
    concatGens422 rfl
    (fun s hs =>
      (NQubitPauliOperator.commutes_iff_symplectic_inner_zero s zE422).mpr (z422_comm s hs))

private lemma witnessE422_mem_centralizer :
    witnessE422 ∈ centralizer steane422Data.concatStabGroup :=
  CentralizerLemmas.mem_centralizer_of_commutes_list witnessE422 steane422Data.concatStabGroup
    concatGens422 rfl
    (fun s hs =>
      (NQubitPauliOperator.commutes_iff_symplectic_inner_zero s witnessE422).mpr
        (witness422_comm s hs))

private lemma witness422_anti_z422 : NQubitPauliGroupElement.Anticommute witnessE422 zE422 :=
  (NQubitPauliOperator.anticommutes_iff_symplectic_inner_one witnessE422 zE422).mpr
    witness422_anti_z422_symp

/-- The explicit weight-6 nontrivial concatenated logical, discharging the final
`concat_hasCodeDistance` input. -/
private lemma steane422_witness :
    ∃ g, IsNontrivialLogicalOperator g steane422Data.concatStabGroup
      ∧ NQubitPauliGroupElement.weight g = 3 * 2 := by
  refine ⟨witnessE422, (IsNontrivialLogicalOperator_iff _ _).mpr
    ⟨witnessE422_mem_centralizer, ?_, ?_⟩, witnessE422_weight⟩
  · exact not_mem_stabilizer_of_anticommutes_centralizer steane422Data.concatStabGroup
      witnessE422 zE422 zE422_mem_centralizer witness422_anti_z422
  · intro s hs h_ops
    exact absurd hs (not_mem_stabilizer_of_anticommutes_centralizer
      steane422Data.concatStabGroup s zE422 zE422_mem_centralizer
      (anticommute_of_operators_eq witnessE422 s zE422 h_ops.symm witness422_anti_z422))

/-- **Steane ⊗ [[4,2,2]] is a `[[28, 2, 6]]` code** (`k₂ = 2`, distance `6 = 3·2`), unconditional.
Discharges M6's `concat_hasCodeDistance` with Steane distance-3 (inner) and `[[4,2,2]]`
distance-2 (outer), the structural generator independence, and the weight-6 witness. -/
theorem steane422_hasCodeDistance_six :
    HasCodeDistance (steane422Data.concatenate steane422_generatorsIndependent) 6 :=
  steane422Data.concat_hasCodeDistance steane422_generatorsIndependent
    rowsLinearIndependent_generatorsList
    stabilizerCode_hasCodeDistance_three FourQubit_4_2_2.code_has_distance_two steane422_witness

end Quantum.StabilizerGroup.Steane7

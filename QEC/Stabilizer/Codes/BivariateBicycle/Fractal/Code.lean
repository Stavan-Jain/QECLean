import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Distance
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Circulant
import QEC.Stabilizer.Framework.Homological.SeparableBBDimension
import QEC.Stabilizer.Framework.Homological.AutoPresentation

/-!
# The fractal family as stabilizer codes with exact distance

The concrete weight-six BB checks have `2*period(s+1)^2` physical qubits,
`2*width(s+1)^2` logical qubits, and exactly the classical seed distance.
The classical minimum is attained, and the separable BB distance theorem
proves equality for every nontrivial Pauli logical operator.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open Quantum.StabilizerGroup
open HomologicalCode
open scoped Matrix

/-- The concrete BB complex has twice the squared classical dimension. -/
theorem chainComplex_finrank_H1 (s : ℕ) :
    Module.finrank (ZMod 2) (chainComplex s).H1 = 2 * width (s + 1) ^ 2 := by
  rw [chainComplex_eq_separable, SeparableBB.finrank_H1]
  have hk : Module.finrank (ZMod 2) (Matrix.circulant (seedCheck s)).mulVecLin.ker =
      width (s + 1) := finrank_seedCheck_kernel s
  rw [hk]
  ring

/-- A nonzero check-kernel word attains the exact classical seed distance. -/
theorem exists_seedCheck_distance_word (s : ℕ) :
    ∃ c : SeedIndex s → ZMod 2, Matrix.circulant (seedCheck s) *ᵥ c = 0 ∧
      c ≠ 0 ∧ hammingNorm c = seedDistance s := by
  obtain ⟨c, hc, hc0, hw⟩ := exists_seedDistance_word s
  refine ⟨reverseWord s c, ?_, ?_, ?_⟩
  · exact (seedCheck_mulVec_eq_zero_iff s _).mpr (by simpa using hc)
  · intro h
    apply hc0
    have hi := congrArg (reverseWord s) h
    simpa using hi
  · rw [hammingNorm_reverseWord, hw]

/-- The exact minimum nontrivial Pauli weight equals the classical seed minimum. -/
theorem chainComplex_pauli_distance (s : ℕ) :
    IsLeast {w : ℕ | ∃ p : NQubitPauliGroupElement (chainComplex s).numQubits,
      IsNontrivialLogicalOperator p (chainComplex s).homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight p = w} (seedDistance s) := by
  rw [chainComplex_eq_separable]
  obtain ⟨c, hc, hc0, hw⟩ := exists_seedCheck_distance_word s
  have hbound := seedCheck_kernel_weight_ge s (seedDistance s) (seedDistance_le_weight s)
  simpa only [min_self] using
    SeparableBB.bb_pauli_distance_eq_min (seedCheck s) (seedCheck s)
      (seedDistance s) (seedDistance s) hbound hbound c hc hc0 hw c hc hc0 hw

/-- The automatically selected independent CSS presentation has the exact
classical seed distance. -/
theorem chainComplex_hasCodeDistance (s : ℕ) :
    HasCodeDistance (chainComplex s).toStabilizerCode (seedDistance s) := by
  have hd := chainComplex_pauli_distance s
  have heq (p : NQubitPauliGroupElement (chainComplex s).numQubits) :
      IsNontrivialLogicalOperator p (chainComplex s).toStabilizerCode.toStabilizerGroup ↔
        IsNontrivialLogicalOperator p (chainComplex s).homologicalStabilizerGroup :=
    (chainComplex s).automaticPresentation.isNontrivialLogicalOperator_iff p
  refine ⟨seedDistance_pos s, ?_, ?_⟩
  · intro p hp _
    exact hd.2 ⟨p, (heq p).mp hp, rfl⟩
  · obtain ⟨p, hp, hw⟩ := hd.1
    exact ⟨p, (heq p).mpr hp, hw⟩

/-- The actual fractal BB stabilizer code with all three parameters proved. -/
noncomputable def stabilizerCodeWithDistance (s : ℕ) :
    StabilizerCodeWithDistance (2 * period (s + 1) ^ 2) (2 * width (s + 1) ^ 2)
      (seedDistance s) :=
  cast (congrArg₂ (fun n k => StabilizerCodeWithDistance n k (seedDistance s))
    (chainComplex_numQubits s) (chainComplex_finrank_H1 s))
    { toStabilizerCode := (chainComplex s).toStabilizerCode
      hasDistance := chainComplex_hasCodeDistance s }

end Quantum.Stabilizer.Homological.BB.Fractal

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFlatBridge
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFlatChecks

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every base-census perturbation of a flat lift is heavy or reaches the common top bank. -/
theorem deep_flat_census_checked (i : Fin 26) (j : Fin 1954) :
    let a := DeepFlatData.firstAt i ^^^ LowCycleNormalization.maskAt j
    let b := DeepFlatData.betaAt i
    22 < bitCount 90 b + 2 * bitCount 90 (a &&& ((2^90-1) ^^^ b)) ∨
      ∃ k : Fin 58130, bottomJoin a b = topBankMask k ∨ bottomJoin (a ^^^ b) b = topBankMask k := by
  fin_cases i
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked0 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked1 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked2 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked3 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked4 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked5 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked6 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked7 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked8 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked9 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked10 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked11 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked12 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked13 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked14 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked15 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked16 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked17 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked18 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked19 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked20 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked21 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked22 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked23 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked24 j)
  · exact bank_case_of_tag _ _ _ (DeepFlatData.checked25 j)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light middle cycle above a certified flat deep shadow reaches the common top bank. -/
theorem deep_flat_complete (i : Fin 26) (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hb : maskOf baseQubitEnum (baseCover.push1 u) = DeepFlatData.betaAt i) :
    ∃ j : Fin 58130, maskOf middleQubitEnum u = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 u) = topBankMask j :=
  deep_flat_complete_of_census deep_flat_census_checked i u hu hw hb

#print axioms deep_flat_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360

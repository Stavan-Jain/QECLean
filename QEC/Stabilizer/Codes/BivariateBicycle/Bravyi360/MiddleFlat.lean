import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleFloorData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomBoundarySheets

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask MiddleFloorData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The seven small stabilizer shadows have flat physical middle-boundary witnesses. -/
theorem middleFlat_checked : ∀ i : Fin 7,
    reconX DeepFlatData.shadowColumns (flatCoeff i) = flatBeta i ∧
      reconX DeepFlatData.sheetColumns (flatCoeff i) &&&
        ((2 ^ 90 - 1) ^^^ flatBeta i) = 0 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A light middle cycle over a small stabilizer shadow is itself a boundary. -/
theorem middle_flat_shadow_boundary (hbase : baseCover.LogicalFloor 8)
    {v : MiddleGroup × Fin 2 → ZMod 2}
    (hv : v ∈ middleComplex.cycles) (hw : middleComplex.chainWeight v ≤ 10)
    (i : Fin 7) (hshadow : maskOf baseQubitEnum (baseCover.push1 v) = flatBeta i) :
    v ∈ middleComplex.boundaries := by
  have hc : flatCoeff i < 2 ^ 90 := Nat.mod_lt _ (Nat.two_pow_pos _)
  exact bottom_flat_shadow_boundary hbase (flatCoeff i) (flatBeta i) hc
    (middleFlat_checked i).1 (middleFlat_checked i).2 hv hw hshadow

end Quantum.Stabilizer.Homological.BB.Bravyi360

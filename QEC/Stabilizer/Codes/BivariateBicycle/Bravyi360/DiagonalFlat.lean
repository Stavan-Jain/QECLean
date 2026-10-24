import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DiagonalData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBoundarySheets

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask DiagonalData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The seven diagonal stabilizer shadows have flat physical boundary witnesses. -/
theorem diagonalFlat_checked : ∀ i : Fin 7,
    reconX TopFlatData.shadowColumns (flatCoeff i) = flatBeta i ∧
      reconX TopFlatData.sheetColumns (flatCoeff i) &&&
        ((2 ^ 180 - 1) ^^^ flatBeta i) = 0 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A light physical cycle over a diagonal stabilizer shadow is itself a boundary. -/
theorem diagonal_flat_shadow_boundary (hmiddle : topCover.LogicalFloor 12)
    {v : Group × Fin 2 → ZMod 2}
    (hv : v ∈ complex.cycles) (hw : complex.chainWeight v ≤ 22)
    (i : Fin 7) (hshadow : maskOf middleQubitEnum (topCover.push1 v) = flatBeta i) :
    v ∈ complex.boundaries := by
  have hc : flatCoeff i < 2 ^ 180 := Nat.mod_lt _ (Nat.two_pow_pos _)
  exact top_flat_shadow_boundary hmiddle (flatCoeff i) (flatBeta i) hc
    (diagonalFlat_checked i).1 (diagonalFlat_checked i).2 hv hw hshadow

end Quantum.Stabilizer.Homological.BB.Bravyi360

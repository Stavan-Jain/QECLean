import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DiagonalBatch
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBridge

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData DiagonalData
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each small logical-shadow certificate uses its actual right-hand side and overflow budget. -/
theorem diagonalEmpty_rhsCap : ∀ i : Fin 36,
    reconX topRColumns (emptyBeta i) = emptyRhs i ∧
      (22 - bitCount 180 (emptyBeta i)) / 2 = 1 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A top cycle of weight at most twenty-two cannot have these diagonal shadows. -/
theorem diagonal_empty_shadow_impossible {v : Group × Fin 2 → ZMod 2}
    (hv : v ∈ complex.cycles) (hw : complex.chainWeight v ≤ 22)
    (i : Fin 36) (hshadow : maskOf middleQubitEnum (topCover.push1 v) = emptyBeta i) : False := by
  apply topFiberEmpty_apply (DiagonalBatch.impossible i) ?_ hv hw hshadow
  exact (diagonalEmpty_rhsCap i).2.le
end Quantum.Stabilizer.Homological.BB.Bravyi360

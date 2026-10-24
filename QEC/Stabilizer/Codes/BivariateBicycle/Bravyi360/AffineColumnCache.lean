import QEC.Stabilizer.Framework.Homological.Certificate.AffineCachedColumns
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DiagonalData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.FiberData

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The common packed E columns agree with the actual fiber map on every point mass. -/
theorem topEColumn_checked : ∀ i : Fin 180,
    DiagonalData.eColumn i = reconX FiberData.topEColumns (2^i.val) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The common packed E-column cache supplies every in-range point-mass image. -/
theorem topEColumn_eq (i : Nat) (hi : i < 180) :
    DiagonalData.eColumn i = reconX FiberData.topEColumns (2^i) := topEColumn_checked ⟨i,hi⟩
end Quantum.Stabilizer.Homological.BB.Bravyi360

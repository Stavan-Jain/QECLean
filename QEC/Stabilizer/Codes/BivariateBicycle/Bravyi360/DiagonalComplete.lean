import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Diagonal
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBridge
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineExceptions

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Shadows of the two diagonal fibers requiring an overflow-three search. -/
noncomputable def diagonalFirstBeta (i : Fin 2) : Nat :=
  if i.val = 0 then 0xc00180000006000c0000000003000600000018003
  else 0x1c0000008000e00000040000040008001200200040009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The two exceptional search inputs are the actual pulled-back base representatives. -/
theorem diagonalFirst_checked : ∀ i : Fin 2,
    maskOf middleQubitEnum (baseCover.pull1
      (chainOfMask baseQubitEnum (LowCycleNormalization.repAt i.val))) = diagonalFirstBeta i ∧
      (22 - bitCount 180 (diagonalFirstBeta i)) / 2 ≤ 3 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Both deeper diagonal affine fibers have no low-weight first sheet. -/
theorem diagonalFirst_empty (i : Fin 2) (word : Nat) (hw : word < 2 ^ 180)
    (he : reconX topEColumns word = reconX topRColumns (diagonalFirstBeta i))
    (hweight : bitCount 180 (outsideMask word (diagonalFirstBeta i)) ≤ 3) : False := by
  fin_cases i
  · exact AffineExceptions.empty655 hw he hweight
  · exact AffineExceptions.empty656 hw he hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light cycle with nonzero diagonal shadow is a physical stabilizer boundary. -/
theorem diagonal_boundary (u : BaseGroup × Fin 2 → ZMod 2) (hu : u ∈ baseComplex.cycles)
    (huw : baseComplex.chainWeight u ≤ 10) (hne : u ≠ 0)
    (v : Group × Fin 2 → ZMod 2) (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22) (hpush : topCover.push1 v = baseCover.pull1 u) :
    v ∈ complex.boundaries := by
  apply diagonal_light_boundary ?_ u hu huw hne v hv hw hpush
  intro i w hwcycle hwsmall hwshadow
  apply topFiberEmpty_apply (diagonalFirst_empty i) (diagonalFirst_checked i).2 hwcycle hwsmall
  rw [hwshadow]
  exact (diagonalFirst_checked i).1

#print axioms diagonal_boundary
end Quantum.Stabilizer.Homological.BB.Bravyi360

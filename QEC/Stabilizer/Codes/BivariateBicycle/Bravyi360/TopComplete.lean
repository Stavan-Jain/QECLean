import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopAssembly
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopNonempty
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineExceptions
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopEmpty0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopEmpty1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopEmpty2

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData TopCaseData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every packed nonempty shadow is included in the proved affine census. -/
theorem topNonempty_membership : ∀ i : Fin 649, nonemptyBeta i ∈ TopNonempty.shadows := by
  have h : (List.range 649).map nonemptyBeta = TopNonempty.shadows := by decide +kernel
  intro i
  rw [← h]
  exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The four exceptional top shadows are excluded by their proved affine searches. -/
theorem topExceptional_empty (i : Fin 4) (word : Nat) (hw : word < 2 ^ 180)
    (he : reconX topEColumns word = reconX topRColumns (exceptionalBeta i))
    (hweight : bitCount 180 (outsideMask word (exceptionalBeta i)) ≤ 3) : False := by
  fin_cases i
  · exact AffineExceptions.empty4 hw he hweight
  · exact AffineExceptions.empty14 hw he hweight
  · exact AffineExceptions.empty18 hw he hweight
  · exact AffineExceptions.empty19 hw he hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every top-bank fiber contains only physical stabilizer boundaries below weight twenty-four. -/
theorem topBank_boundary (i : Fin 58130) (v : Group × Fin 2 → ZMod 2)
    (hv : v ∈ complex.cycles) (hw : complex.chainWeight v ≤ 22)
    (hshadow : maskOf middleQubitEnum (topCover.push1 v) = topBankMask i) :
    v ∈ complex.boundaries := by
  apply topBank_boundary_of_families middle_logical_floor
    (fun j => TopNonempty.boundary_of_mem (topNonempty_membership j))
    topExceptional_empty
    (fun j word hw he hweight => TopEmpty.cap0_impossible j word hw he hweight)
    (fun j word hw he hweight => TopEmpty.cap1_impossible j word hw he hweight)
    (fun j word hw he hweight => TopEmpty.cap2_impossible j word hw he hweight)
    i hv hw hshadow

#print axioms topBank_boundary
end Quantum.Stabilizer.Homological.BB.Bravyi360

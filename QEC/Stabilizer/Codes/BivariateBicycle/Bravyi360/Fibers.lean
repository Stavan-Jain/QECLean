import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.FiberData
import QEC.Stabilizer.Framework.Homological.Certificate.MaskFiber
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Sparse
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleSparse

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The bottom E map in certificate coordinates. -/
noncomputable def bottomE : (BaseGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (MiddleGroup → ZMod 2) :=
  reconLinear baseQubitEnum middleFaceEnum bottomEColumns

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The bottom R map in certificate coordinates. -/
noncomputable def bottomR : (BaseGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (MiddleGroup → ZMod 2) :=
  reconLinear baseQubitEnum middleFaceEnum bottomRColumns

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse numeric columns certify the bottom carry equation on every qubit. -/
theorem bottom_fiber_columns : ∀ q : MiddleGroup × Fin 2,
    (reconX bottomEColumns
      (if baseSection (baseProjection q.1) = q.1 then
        2 ^ (baseQubitEnum (baseProjection q.1, q.2)).val else 0)) ^^^
      reconX bottomRColumns (2 ^ (baseQubitEnum (baseProjection q.1, q.2)).val) =
        middleSyndromeMask q := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse point-mass verification of the bottom lift equation. -/
theorem bottom_fiber_basis (q : MiddleGroup × Fin 2) :
    bottomE (baseCover.sheet0 (Pi.single q 1)) +
        bottomR (baseCover.sheet0 (Pi.single q 1) + baseCover.sheet1 (Pi.single q 1)) =
      fun h => SmallCycle.termAt baseCover.Ac baseCover.Bc q h := by
  have hsyndrome : (fun h => SmallCycle.termAt baseCover.Ac baseCover.Bc q h) =
      middleComplex.boundary1 (Pi.single q 1) := by
    funext h
    exact (SmallCycle.bbBoundary1Fn_single_point middleA middleB q h).symm
  rw [hsyndrome, baseCover.sheets_add_eq_push, baseCover.push1_single,
    baseCover.sheet0_single]
  apply maskOf_injective middleFaceEnum
  rw [maskOf_add, bottomE, bottomR,
    maskOf_reconLinear _ _ _ _ bottomEColumns_bounded,
    maskOf_reconLinear _ _ _ _ bottomRColumns_bounded,
    maskOf_single, maskOf_middle_boundary1_single]
  have hmask : maskOf baseQubitEnum
      (if baseCover.sec (baseCover.proj q.1) = q.1 then
        Pi.single (baseCover.proj q.1, q.2) 1 else 0) =
      if baseSection (baseProjection q.1) = q.1 then
        2 ^ (baseQubitEnum (baseProjection q.1, q.2)).val else 0 := by
    simp only [baseCover]
    split_ifs <;> simp only [maskOf_single, maskOf_zero]
  rw [hmask]
  exact bottom_fiber_columns q

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every bottom cycle satisfies the finite carry equation used by the certificates. -/
theorem bottom_fiber_equation {v : MiddleGroup × Fin 2 → ZMod 2}
    (hv : v ∈ middleComplex.cycles) :
    reconX bottomEColumns (maskOf baseQubitEnum (baseCover.sheet0 v)) =
      reconX bottomRColumns (maskOf baseQubitEnum (baseCover.push1 v)) := by
  have h := congrArg (maskOf middleFaceEnum)
    (baseCover.sheet_equation_of_basis bottomE bottomR bottom_fiber_basis hv)
  simpa only [bottomE, bottomR,
    maskOf_reconLinear baseQubitEnum middleFaceEnum bottomEColumns _ bottomEColumns_bounded,
    maskOf_reconLinear baseQubitEnum middleFaceEnum bottomRColumns _ bottomRColumns_bounded] using h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The top E map in certificate coordinates. -/
noncomputable def topE : (MiddleGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (Group → ZMod 2) :=
  reconLinear middleQubitEnum faceEnum topEColumns

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The top R map in certificate coordinates. -/
noncomputable def topR : (MiddleGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (Group → ZMod 2) :=
  reconLinear middleQubitEnum faceEnum topRColumns

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse numeric columns certify the top carry equation on every qubit. -/
theorem top_fiber_columns : ∀ q : Group × Fin 2,
    (reconX topEColumns
      (if topSection (topProjection q.1) = q.1 then
        2 ^ (middleQubitEnum (topProjection q.1, q.2)).val else 0)) ^^^
      reconX topRColumns (2 ^ (middleQubitEnum (topProjection q.1, q.2)).val) =
        syndromeMask q := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse point-mass verification of the top lift equation. -/
theorem top_fiber_basis (q : Group × Fin 2) :
    topE (topCover.sheet0 (Pi.single q 1)) +
        topR (topCover.sheet0 (Pi.single q 1) + topCover.sheet1 (Pi.single q 1)) =
      fun h => SmallCycle.termAt topCover.Ac topCover.Bc q h := by
  have hsyndrome : (fun h => SmallCycle.termAt topCover.Ac topCover.Bc q h) =
      complex.boundary1 (Pi.single q 1) := by
    funext h
    exact (SmallCycle.bbBoundary1Fn_single_point A B q h).symm
  rw [hsyndrome, topCover.sheets_add_eq_push, topCover.push1_single,
    topCover.sheet0_single]
  apply maskOf_injective faceEnum
  rw [maskOf_add, topE, topR,
    maskOf_reconLinear _ _ _ _ topEColumns_bounded,
    maskOf_reconLinear _ _ _ _ topRColumns_bounded,
    maskOf_single, maskOf_boundary1_single]
  have hmask : maskOf middleQubitEnum
      (if topCover.sec (topCover.proj q.1) = q.1 then
        Pi.single (topCover.proj q.1, q.2) 1 else 0) =
      if topSection (topProjection q.1) = q.1 then
        2 ^ (middleQubitEnum (topProjection q.1, q.2)).val else 0 := by
    simp only [topCover]
    split_ifs <;> simp only [maskOf_single, maskOf_zero]
  rw [hmask]
  exact top_fiber_columns q

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every top cycle satisfies the finite carry equation used by the certificates. -/
theorem top_fiber_equation {v : Group × Fin 2 → ZMod 2}
    (hv : v ∈ complex.cycles) :
    reconX topEColumns (maskOf middleQubitEnum (topCover.sheet0 v)) =
      reconX topRColumns (maskOf middleQubitEnum (topCover.push1 v)) := by
  have h := congrArg (maskOf faceEnum)
    (topCover.sheet_equation_of_basis topE topR top_fiber_basis hv)
  simpa only [topE, topR,
    maskOf_reconLinear middleQubitEnum faceEnum topEColumns _ topEColumns_bounded,
    maskOf_reconLinear middleQubitEnum faceEnum topRColumns _ topRColumns_bounded] using h

end Quantum.Stabilizer.Homological.BB.Bravyi360

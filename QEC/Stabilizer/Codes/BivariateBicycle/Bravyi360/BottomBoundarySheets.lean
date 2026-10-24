import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomBoundarySheetsData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleSparse
import QEC.Stabilizer.Framework.Homological.Certificate.MaskSparseSheets
import QEC.Stabilizer.Framework.Homological.BBFlatLift

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask DeepFlatData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Both bottom boundary restriction matrices preserve the 90-bit syndrome width. -/
theorem bottomBoundarySheets_bounded :
    (∀ p ∈ sheetColumns, p.1 < 90 ∧ p.2 < 2 ^ 90) ∧
      (∀ p ∈ shadowColumns, p.1 < 90 ∧ p.2 < 2 ^ 90) := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The first matrix is the first sheet of each physical face boundary. -/
theorem bottomBoundarySheet_columns : ∀ g : MiddleGroup,
    maskOf baseQubitEnum (baseCover.sheet0 (middleFaceRow g)) =
      reconX sheetColumns (2 ^ (middleFaceEnum g).val) := by
  have h : ∀ g : MiddleGroup,
      xorList ((middleFacePoints g).map fun q =>
        if baseSection (baseProjection q.1) = q.1 then
          2 ^ (baseQubitEnum (baseProjection q.1, q.2)).val else 0) =
        reconX sheetColumns (2 ^ (middleFaceEnum g).val) := by decide +kernel
  intro g
  rw [middleFaceRow_eq_sum, baseCover.maskOf_sheet0_sum_points]
  exact h g

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The second matrix is the projection of each physical face boundary. -/
theorem bottomBoundaryShadow_columns : ∀ g : MiddleGroup,
    maskOf baseQubitEnum (baseCover.sheet0 (middleFaceRow g) + baseCover.sheet1 (middleFaceRow g)) =
      reconX shadowColumns (2 ^ (middleFaceEnum g).val) := by
  have h : ∀ g : MiddleGroup,
      xorList ((middleFacePoints g).map fun q =>
        2 ^ (baseQubitEnum (baseProjection q.1, q.2)).val) =
        reconX shadowColumns (2 ^ (middleFaceEnum g).val) := by decide +kernel
  intro g
  rw [baseCover.sheets_add_eq_push, middleFaceRow_eq_sum, baseCover.maskOf_push1_sum_points]
  exact h g

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The first packed restriction matrix describes every physical face combination. -/
theorem bottomBoundarySheet_map (f : MiddleGroup → ZMod 2) :
    baseCover.sheet0 (middleComplex.boundary2 f) = reconLinear middleFaceEnum baseQubitEnum sheetColumns f := by
  have h : ∀ f : MiddleGroup → ZMod 2,
      baseCover.sheet0 (middleComplex.boundary2 f) = reconLinear middleFaceEnum baseQubitEnum sheetColumns f := by
    apply funLiftF2
    · exact congrArg baseCover.sheet0 middleComplex.boundary2.map_zero
    · exact (reconLinear middleFaceEnum baseQubitEnum sheetColumns).map_zero
    · intro a b
      exact (congrArg baseCover.sheet0 (middleComplex.boundary2.map_add a b)).trans
        (baseCover.sheet0_add _ _)
    · intro a b
      exact (reconLinear middleFaceEnum baseQubitEnum sheetColumns).map_add a b
    · intro g
      apply Eq.trans (congrArg baseCover.sheet0 (middleBoundary2_single_eq_faceRow g))
      change baseCover.sheet0 (middleFaceRow g) = chainOfMask baseQubitEnum
        (reconX sheetColumns (maskOf middleFaceEnum (Pi.single g 1)))
      apply maskOf_injective baseQubitEnum
      rw [maskOf_chainOfMask baseQubitEnum
        (reconX_lt sheetColumns _ 90 (fun p hp => (bottomBoundarySheets_bounded.1 p hp).2)),
        maskOf_single]
      exact bottomBoundarySheet_columns g
  exact h f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The second packed restriction matrix describes every projected face combination. -/
theorem bottomBoundaryShadow_map (f : MiddleGroup → ZMod 2) :
    baseCover.push1 (middleComplex.boundary2 f) = reconLinear middleFaceEnum baseQubitEnum shadowColumns f := by
  have h : ∀ f : MiddleGroup → ZMod 2,
      baseCover.push1 (middleComplex.boundary2 f) = reconLinear middleFaceEnum baseQubitEnum shadowColumns f := by
    apply funLiftF2
    · exact (congrArg baseCover.push1 middleComplex.boundary2.map_zero).trans baseCover.push1.map_zero
    · exact (reconLinear middleFaceEnum baseQubitEnum shadowColumns).map_zero
    · intro a b
      exact (congrArg baseCover.push1 (middleComplex.boundary2.map_add a b)).trans
        (baseCover.push1.map_add _ _)
    · intro a b
      exact (reconLinear middleFaceEnum baseQubitEnum shadowColumns).map_add a b
    · intro g
      apply Eq.trans (congrArg baseCover.push1 (middleBoundary2_single_eq_faceRow g))
      change baseCover.push1 (middleFaceRow g) = chainOfMask baseQubitEnum
        (reconX shadowColumns (maskOf middleFaceEnum (Pi.single g 1)))
      apply maskOf_injective baseQubitEnum
      rw [maskOf_chainOfMask baseQubitEnum
        (reconX_lt shadowColumns _ 90 (fun p hp => (bottomBoundarySheets_bounded.2 p hp).2)),
        maskOf_single, ← baseCover.sheets_add_eq_push]
      exact bottomBoundaryShadow_columns g
  exact h f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading the first sheet of a packed face combination computes its certified matrix. -/
theorem bottomBoundarySheet_mask (coeff : Nat) (hc : coeff < 2 ^ 90) :
    maskOf baseQubitEnum (baseCover.sheet0 (middleComplex.boundary2 (chainOfMask middleFaceEnum coeff))) =
      reconX sheetColumns coeff := by
  calc
    _ = maskOf baseQubitEnum (reconLinear middleFaceEnum baseQubitEnum sheetColumns
          (chainOfMask middleFaceEnum coeff)) := congrArg (maskOf baseQubitEnum) (bottomBoundarySheet_map _)
    _ = reconX sheetColumns (maskOf middleFaceEnum (chainOfMask middleFaceEnum coeff)) :=
      maskOf_reconLinear _ _ _ _ (fun p hp => (bottomBoundarySheets_bounded.1 p hp).2)
    _ = reconX sheetColumns coeff := congrArg (reconX sheetColumns) (maskOf_chainOfMask middleFaceEnum hc)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading the shadow of a packed face combination computes its certified matrix. -/
theorem bottomBoundaryShadow_mask (coeff : Nat) (hc : coeff < 2 ^ 90) :
    maskOf baseQubitEnum (baseCover.push1 (middleComplex.boundary2 (chainOfMask middleFaceEnum coeff))) =
      reconX shadowColumns coeff := by
  calc
    _ = maskOf baseQubitEnum (reconLinear middleFaceEnum baseQubitEnum shadowColumns
          (chainOfMask middleFaceEnum coeff)) := congrArg (maskOf baseQubitEnum) (bottomBoundaryShadow_map _)
    _ = reconX shadowColumns (maskOf middleFaceEnum (chainOfMask middleFaceEnum coeff)) :=
      maskOf_reconLinear _ _ _ _ (fun p hp => (bottomBoundarySheets_bounded.2 p hp).2)
    _ = reconX shadowColumns coeff := congrArg (reconX shadowColumns) (maskOf_chainOfMask middleFaceEnum hc)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed flat boundary certificate excludes every nontrivial lift below weight24. -/
theorem bottom_flat_shadow_boundary (hbase : baseCover.LogicalFloor 8)
    (coeff beta : Nat) (hc : coeff < 2 ^ 90)
    (hpush : reconX shadowColumns coeff = beta)
    (hflat : reconX sheetColumns coeff &&& ((2 ^ 90 - 1) ^^^ beta) = 0)
    {v : MiddleGroup × Fin 2 → ZMod 2} (hv : v ∈ middleComplex.cycles)
    (hw : middleComplex.chainWeight v ≤ 10)
    (hshadow : maskOf baseQubitEnum (baseCover.push1 v) = beta) :
    v ∈ middleComplex.boundaries := by
  by_contra hn
  let c := middleComplex.boundary2 (chainOfMask middleFaceEnum coeff)
  have hb : c ∈ middleComplex.boundaries := ⟨chainOfMask middleFaceEnum coeff, rfl⟩
  have hp : baseCover.push1 v = baseCover.push1 c := by
    apply maskOf_injective baseQubitEnum
    exact hshadow.trans ((bottomBoundaryShadow_mask coeff hc).trans hpush).symm
  have hf : ∀ q, baseCover.sheet0 c q ≠ 0 → baseCover.push1 c q ≠ 0 := by
    apply support_subset_of_mask_restrict_zero baseQubitEnum
    change maskOf baseQubitEnum (baseCover.sheet0 (middleComplex.boundary2 (chainOfMask middleFaceEnum coeff))) &&&
      ((2 ^ 90 - 1) ^^^ maskOf baseQubitEnum
        (baseCover.push1 (middleComplex.boundary2 (chainOfMask middleFaceEnum coeff)))) = 0
    rw [bottomBoundarySheet_mask coeff hc, bottomBoundaryShadow_mask coeff hc, hpush]
    exact hflat
  have hbound := baseCover.chainWeight_ge_double_of_flat_boundary hbase hb hf hv hn hp
  change 16 ≤ middleComplex.chainWeight v at hbound
  omega


end Quantum.Stabilizer.Homological.BB.Bravyi360

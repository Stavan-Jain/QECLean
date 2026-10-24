import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBoundarySheetsData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Sparse
import QEC.Stabilizer.Framework.Homological.Certificate.MaskSparseSheets
import QEC.Stabilizer.Framework.Homological.BBFlatLift

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask TopFlatData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Both top boundary restriction matrices preserve the 180-bit syndrome width. -/
theorem topBoundarySheets_bounded :
    (∀ p ∈ sheetColumns, p.1 < 180 ∧ p.2 < 2 ^ 180) ∧
      (∀ p ∈ shadowColumns, p.1 < 180 ∧ p.2 < 2 ^ 180) := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The first matrix is the first sheet of each physical face boundary. -/
theorem topBoundarySheet_columns : ∀ g : Group,
    maskOf middleQubitEnum (topCover.sheet0 (faceRow g)) =
      reconX sheetColumns (2 ^ (faceEnum g).val) := by
  have h : ∀ g : Group,
      xorList ((facePoints g).map fun q =>
        if topSection (topProjection q.1) = q.1 then
          2 ^ (middleQubitEnum (topProjection q.1, q.2)).val else 0) =
        reconX sheetColumns (2 ^ (faceEnum g).val) := by decide +kernel
  intro g
  rw [faceRow_eq_sum, topCover.maskOf_sheet0_sum_points]
  exact h g

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The second matrix is the projection of each physical face boundary. -/
theorem topBoundaryShadow_columns : ∀ g : Group,
    maskOf middleQubitEnum (topCover.sheet0 (faceRow g) + topCover.sheet1 (faceRow g)) =
      reconX shadowColumns (2 ^ (faceEnum g).val) := by
  have h : ∀ g : Group,
      xorList ((facePoints g).map fun q =>
        2 ^ (middleQubitEnum (topProjection q.1, q.2)).val) =
        reconX shadowColumns (2 ^ (faceEnum g).val) := by decide +kernel
  intro g
  rw [topCover.sheets_add_eq_push, faceRow_eq_sum, topCover.maskOf_push1_sum_points]
  exact h g

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The first packed restriction matrix describes every physical face combination. -/
theorem topBoundarySheet_map (f : Group → ZMod 2) :
    topCover.sheet0 (complex.boundary2 f) = reconLinear faceEnum middleQubitEnum sheetColumns f := by
  have h : ∀ f : Group → ZMod 2,
      topCover.sheet0 (complex.boundary2 f) = reconLinear faceEnum middleQubitEnum sheetColumns f := by
    apply funLiftF2
    · exact congrArg topCover.sheet0 complex.boundary2.map_zero
    · exact (reconLinear faceEnum middleQubitEnum sheetColumns).map_zero
    · intro a b
      exact (congrArg topCover.sheet0 (complex.boundary2.map_add a b)).trans
        (topCover.sheet0_add _ _)
    · intro a b
      exact (reconLinear faceEnum middleQubitEnum sheetColumns).map_add a b
    · intro g
      apply Eq.trans (congrArg topCover.sheet0 (boundary2_single_eq_faceRow g))
      change topCover.sheet0 (faceRow g) = chainOfMask middleQubitEnum
        (reconX sheetColumns (maskOf faceEnum (Pi.single g 1)))
      apply maskOf_injective middleQubitEnum
      rw [maskOf_chainOfMask middleQubitEnum
        (reconX_lt sheetColumns _ 180 (fun p hp => (topBoundarySheets_bounded.1 p hp).2)),
        maskOf_single]
      exact topBoundarySheet_columns g
  exact h f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The second packed restriction matrix describes every projected face combination. -/
theorem topBoundaryShadow_map (f : Group → ZMod 2) :
    topCover.push1 (complex.boundary2 f) = reconLinear faceEnum middleQubitEnum shadowColumns f := by
  have h : ∀ f : Group → ZMod 2,
      topCover.push1 (complex.boundary2 f) = reconLinear faceEnum middleQubitEnum shadowColumns f := by
    apply funLiftF2
    · exact (congrArg topCover.push1 complex.boundary2.map_zero).trans topCover.push1.map_zero
    · exact (reconLinear faceEnum middleQubitEnum shadowColumns).map_zero
    · intro a b
      exact (congrArg topCover.push1 (complex.boundary2.map_add a b)).trans
        (topCover.push1.map_add _ _)
    · intro a b
      exact (reconLinear faceEnum middleQubitEnum shadowColumns).map_add a b
    · intro g
      apply Eq.trans (congrArg topCover.push1 (boundary2_single_eq_faceRow g))
      change topCover.push1 (faceRow g) = chainOfMask middleQubitEnum
        (reconX shadowColumns (maskOf faceEnum (Pi.single g 1)))
      apply maskOf_injective middleQubitEnum
      rw [maskOf_chainOfMask middleQubitEnum
        (reconX_lt shadowColumns _ 180 (fun p hp => (topBoundarySheets_bounded.2 p hp).2)),
        maskOf_single, ← topCover.sheets_add_eq_push]
      exact topBoundaryShadow_columns g
  exact h f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading the first sheet of a packed face combination computes its certified matrix. -/
theorem topBoundarySheet_mask (coeff : Nat) (hc : coeff < 2 ^ 180) :
    maskOf middleQubitEnum (topCover.sheet0 (complex.boundary2 (chainOfMask faceEnum coeff))) =
      reconX sheetColumns coeff := by
  calc
    _ = maskOf middleQubitEnum (reconLinear faceEnum middleQubitEnum sheetColumns
          (chainOfMask faceEnum coeff)) := congrArg (maskOf middleQubitEnum) (topBoundarySheet_map _)
    _ = reconX sheetColumns (maskOf faceEnum (chainOfMask faceEnum coeff)) :=
      maskOf_reconLinear _ _ _ _ (fun p hp => (topBoundarySheets_bounded.1 p hp).2)
    _ = reconX sheetColumns coeff := congrArg (reconX sheetColumns) (maskOf_chainOfMask faceEnum hc)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading the shadow of a packed face combination computes its certified matrix. -/
theorem topBoundaryShadow_mask (coeff : Nat) (hc : coeff < 2 ^ 180) :
    maskOf middleQubitEnum (topCover.push1 (complex.boundary2 (chainOfMask faceEnum coeff))) =
      reconX shadowColumns coeff := by
  calc
    _ = maskOf middleQubitEnum (reconLinear faceEnum middleQubitEnum shadowColumns
          (chainOfMask faceEnum coeff)) := congrArg (maskOf middleQubitEnum) (topBoundaryShadow_map _)
    _ = reconX shadowColumns (maskOf faceEnum (chainOfMask faceEnum coeff)) :=
      maskOf_reconLinear _ _ _ _ (fun p hp => (topBoundarySheets_bounded.2 p hp).2)
    _ = reconX shadowColumns coeff := congrArg (reconX shadowColumns) (maskOf_chainOfMask faceEnum hc)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed flat boundary certificate excludes every nontrivial lift below weight24. -/
theorem top_flat_shadow_boundary (hmiddle : topCover.LogicalFloor 12)
    (coeff beta : Nat) (hc : coeff < 2 ^ 180)
    (hpush : reconX shadowColumns coeff = beta)
    (hflat : reconX sheetColumns coeff &&& ((2 ^ 180 - 1) ^^^ beta) = 0)
    {v : Group × Fin 2 → ZMod 2} (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22)
    (hshadow : maskOf middleQubitEnum (topCover.push1 v) = beta) :
    v ∈ complex.boundaries := by
  by_contra hn
  let c := complex.boundary2 (chainOfMask faceEnum coeff)
  have hb : c ∈ complex.boundaries := ⟨chainOfMask faceEnum coeff, rfl⟩
  have hp : topCover.push1 v = topCover.push1 c := by
    apply maskOf_injective middleQubitEnum
    exact hshadow.trans ((topBoundaryShadow_mask coeff hc).trans hpush).symm
  have hf : ∀ q, topCover.sheet0 c q ≠ 0 → topCover.push1 c q ≠ 0 := by
    apply support_subset_of_mask_restrict_zero middleQubitEnum
    change maskOf middleQubitEnum (topCover.sheet0 (complex.boundary2 (chainOfMask faceEnum coeff))) &&&
      ((2 ^ 180 - 1) ^^^ maskOf middleQubitEnum
        (topCover.push1 (complex.boundary2 (chainOfMask faceEnum coeff)))) = 0
    rw [topBoundarySheet_mask coeff hc, topBoundaryShadow_mask coeff hc, hpush]
    exact hflat
  have hbound := topCover.chainWeight_ge_double_of_flat_boundary hmiddle hb hf hv hn hp
  change 24 ≤ complex.chainWeight v at hbound
  omega

end Quantum.Stabilizer.Homological.BB.Bravyi360

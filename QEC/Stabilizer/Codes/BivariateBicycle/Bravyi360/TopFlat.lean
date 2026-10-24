import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFlatChecks
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBoundarySheets
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBank
import QEC.Stabilizer.Framework.Homological.Certificate.BatchReconLane

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask PackedDigits
set_option maxRecDepth 200000
set_option exponentiation.threshold 1000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every flat boundary coefficient is bounded by its180-bit lane. -/
theorem topFlatCoeff_lt (i : Nat) : TopFlatData.coeffAt i < 2 ^ 180 :=
  lane_lt _ _ _

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each packed batch certifies the two matrix properties for its individual witnesses. -/
theorem topFlat_matrix_checked (i : Fin 30338) :
    reconX TopFlatData.shadowColumns (TopFlatData.coeffAt i) = TopFlatData.betaAt i ∧
      reconX TopFlatData.sheetColumns (TopFlatData.coeffAt i) &&&
        ((2 ^ 180 - 1) ^^^ TopFlatData.betaAt i) = 0 := by
  let b : Fin 30 := ⟨i.val / 1024, by omega⟩
  have h := TopFlatData.all_checked b
  simp only [TopFlatData.checkFlatBatch, Bool.and_eq_true, Nat.beq_eq] at h
  exact batchFlat_sound 180 10 (TopFlatData.coeffChunk b) (TopFlatData.betaChunk b)
    (by decide) (TopFlatData.coeffChunks_bounded b)
    TopFlatData.sheetColumns TopFlatData.shadowColumns
    topBoundarySheets_bounded.1 topBoundarySheets_bounded.2 h.1 h.2
    (i.val % 1024) (Nat.mod_lt _ (by decide))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- All30338 flat cases in the top bank are stabilizer boundaries at weight at most22. -/
theorem topFlat_boundary (hmiddle : topCover.LogicalFloor 12) (i : Fin 30338)
    {v : Group × Fin 2 → ZMod 2} (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22)
    (hshadow : maskOf middleQubitEnum (topCover.push1 v) = TopFlatData.betaAt i) :
    v ∈ complex.boundaries := by
  exact top_flat_shadow_boundary hmiddle (TopFlatData.coeffAt i) (TopFlatData.betaAt i)
    (topFlatCoeff_lt i) (topFlat_matrix_checked i).1 (topFlat_matrix_checked i).2 hv hw hshadow

end Quantum.Stabilizer.Homological.BB.Bravyi360

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BaseFloorChecks
import QEC.Stabilizer.Framework.Homological.Certificate.MaskSpan

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
open F2Mask.Trellis.Bravyi90
set_option maxRecDepth 10000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading the base syndrome reconstruction gives the packed syndrome itself. -/
theorem baseCensus_mask (v : BaseGroup × Fin 2 → ZMod 2) :
    maskOf baseFaceEnum (reconLinear baseQubitEnum baseFaceEnum cycleSyndrome v) =
      reconX cycleSyndrome (maskOf baseQubitEnum v) :=
  maskOf_reconLinear baseQubitEnum baseFaceEnum cycleSyndrome v baseCensusSyndrome_bounded

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The census syndrome map is the actual first boundary map of the base code. -/
theorem baseBoundary1_eq_reconLinear : baseComplex.boundary1 =
    reconLinear baseQubitEnum baseFaceEnum cycleSyndrome := by
  apply linearMap_eq_of_single
  intro q
  apply maskOf_injective baseFaceEnum
  change maskOf baseFaceEnum (baseComplex.boundary1 (Pi.single q 1)) =
    maskOf baseFaceEnum (chainOfMask baseFaceEnum
      (reconX cycleSyndrome (maskOf baseQubitEnum (Pi.single q 1))))
  rw [maskOf_base_boundary1_single,
    maskOf_chainOfMask baseFaceEnum (reconX_lt cycleSyndrome _ 45 baseCensusSyndrome_bounded),
    maskOf_single, baseCensusSyndrome_columns]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The census boundary generators are boundaries of the physical base code. -/
theorem baseBoundaryWindow_mem : ∀ p ∈ baseBoundaryWindow,
    chainOfMask baseQubitEnum p.2 ∈ baseComplex.boundaries := by
  intro p hp
  obtain ⟨i, hi⟩ := baseBoundaryWindow_columns p hp
  rw [hi, ← baseMaskOf_faceRow, chainOfMask_maskOf]
  exact ⟨Pi.single (baseFaceEnum.symm i) 1, baseBoundary2_single_eq_faceRow _⟩

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light physical base cycle occurs in the independently complete packed census. -/
theorem base_cycle_mem_census {v : BaseGroup × Fin 2 → ZMod 2}
    (hv : v ∈ baseComplex.cycles) (hw : baseComplex.chainWeight v ≤ 10) :
    maskOf baseQubitEnum v ∈ allBaseCycles10 := by
  have hs : reconX cycleSyndrome (maskOf baseQubitEnum v) = 0 := by
    have he := LinearMap.congr_fun baseBoundary1_eq_reconLinear v
    have hz : reconLinear baseQubitEnum baseFaceEnum cycleSyndrome v = 0 :=
      he.symm.trans (show baseComplex.boundary1 v = 0 from hv)
    exact (baseCensus_mask v).symm.trans
      ((congrArg (maskOf baseFaceEnum) hz).trans (maskOf_zero baseFaceEnum))
  apply baseCycle10_complete (maskOf_lt baseQubitEnum v) hs
  rw [← card_support_eq_bitCount baseQubitEnum]
  exact hw

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every cycle in the physical base code of weight below eight is a boundary. -/
theorem base_cycle_lt_eight_boundary {v : BaseGroup × Fin 2 → ZMod 2}
    (hv : v ∈ baseComplex.cycles) (hw : baseComplex.chainWeight v < 8) :
    v ∈ baseComplex.boundaries := by
  have hs : reconX cycleSyndrome (maskOf baseQubitEnum v) = 0 := by
    have he := LinearMap.congr_fun baseBoundary1_eq_reconLinear v
    have hz : reconLinear baseQubitEnum baseFaceEnum cycleSyndrome v = 0 :=
      he.symm.trans (show baseComplex.boundary1 v = 0 from hv)
    exact (baseCensus_mask v).symm.trans
      ((congrArg (maskOf baseFaceEnum) hz).trans (maskOf_zero baseFaceEnum))
  have hweight : bitCount 90 (maskOf baseQubitEnum v) < 8 := by
    rw [← card_support_eq_bitCount baseQubitEnum]
    exact hw
  obtain ⟨coeff, hc⟩ := base_floor_eight (maskOf_lt baseQubitEnum v) hs hweight
  have hb := chainOfMask_reconX_mem baseQubitEnum baseComplex.boundaries
    baseBoundaryWindow baseBoundaryWindow_mem coeff
  rwa [hc, chainOfMask_maskOf] at hb

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The bottom quotient has logical weight at least eight. -/
theorem base_logical_floor : baseCover.LogicalFloor 8 := by
  intro v hv hn
  change 8 ≤ baseComplex.chainWeight v
  by_contra h
  exact hn (base_cycle_lt_eight_boundary hv (by omega))

end Quantum.Stabilizer.Homological.BB.Bravyi360

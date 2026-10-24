import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ReachabilityChecks

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask ReachabilityData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading back the candidate-space reconstruction gives its packed linear map. -/
theorem mask_reachableMap (c : Fin 43 → ZMod 2) :
    maskOf baseQubitEnum (reachableMap c) =
      reconX reachableGenerators (maskOf (Equiv.refl (Fin 43)) c) :=
  maskOf_reconLinear _ _ _ _ reachableGenerators_bounded

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading back the projected-cycle decoder gives its packed linear map. -/
theorem mask_reachableDecode (c : BaseGroup × Fin 2 → ZMod 2) :
    maskOf (Equiv.refl (Fin 43)) (reachableDecode c) =
      reconX reachableDecoder (maskOf baseQubitEnum c) :=
  maskOf_reconLinear _ _ _ _ reachableDecoder_bounded

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reading back the syndrome correction gives its packed linear map. -/
theorem mask_reachableResidual (c : Group → ZMod 2) :
    maskOf baseQubitEnum (reachableResidual c) =
      reconX reachableCorrection (maskOf faceEnum c) :=
  maskOf_reconLinear _ _ _ _ reachableCorrection_bounded

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse point-mass certificate for the projected cycle image. -/
theorem reachable_basis (q : Group × Fin 2) :
    reachableMap (reachableDecode (baseCover.push1 (topCover.push1 (Pi.single q 1)))) +
        reachableResidual (complex.boundary1 (Pi.single q 1)) =
      baseCover.push1 (topCover.push1 (Pi.single q 1)) := by
  rw [topCover.push1_single, baseCover.push1_single]
  apply maskOf_injective baseQubitEnum
  rw [maskOf_add, mask_reachableMap, mask_reachableDecode, mask_reachableResidual,
    maskOf_single, maskOf_boundary1_single]
  exact reachable_columns q

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every 360-qubit cycle projects into the certified43-dimensional bottom space. -/
theorem bottomShadow_mem_reachable {v : Group × Fin 2 → ZMod 2}
    (hv : v ∈ complex.cycles) :
    XorSpan (reachableGenerators.map Prod.snd)
      (maskOf baseQubitEnum (baseCover.push1 (topCover.push1 v))) := by
  have hfull : ∀ w : Group × Fin 2 → ZMod 2,
      reachableMap (reachableDecode (baseCover.push1 (topCover.push1 w))) +
          reachableResidual (complex.boundary1 w) = baseCover.push1 (topCover.push1 w) := by
    apply funLiftF2
    · have hp := (congrArg baseCover.push1 topCover.push1.map_zero).trans baseCover.push1.map_zero
      have hd := (congrArg reachableDecode hp).trans reachableDecode.map_zero
      have hm := (congrArg reachableMap hd).trans reachableMap.map_zero
      have hr := (congrArg reachableResidual complex.boundary1.map_zero).trans reachableResidual.map_zero
      exact (congrArg₂ (fun a b : BaseGroup × Fin 2 → ZMod 2 => a + b) hm hr).trans (add_zero 0)
    · exact (congrArg baseCover.push1 topCover.push1.map_zero).trans baseCover.push1.map_zero
    · intro a b
      have hp := (congrArg baseCover.push1 (topCover.push1.map_add a b)).trans
        (baseCover.push1.map_add _ _)
      have hd := (congrArg reachableDecode hp).trans (reachableDecode.map_add _ _)
      have hm := (congrArg reachableMap hd).trans (reachableMap.map_add _ _)
      have hr := (congrArg reachableResidual (complex.boundary1.map_add a b)).trans
        (reachableResidual.map_add _ _)
      exact (congrArg₂ (fun a b : BaseGroup × Fin 2 → ZMod 2 => a + b) hm hr).trans (by abel)
    · intro a b
      exact (congrArg baseCover.push1 (topCover.push1.map_add a b)).trans
        (baseCover.push1.map_add _ _)
    · exact reachable_basis
  have h := hfull v
  have hz : reachableResidual (complex.boundary1 v) = 0 :=
    (congrArg reachableResidual (show complex.boundary1 v = 0 from hv)).trans
      reachableResidual.map_zero
  rw [hz, add_zero] at h
  have hm := congrArg (maskOf baseQubitEnum) h
  rw [mask_reachableMap] at hm
  rw [← hm]
  exact reconX_mem_span _ _

end Quantum.Stabilizer.Homological.BB.Bravyi360

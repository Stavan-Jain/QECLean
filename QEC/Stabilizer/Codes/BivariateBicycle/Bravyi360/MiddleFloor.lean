import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BaseFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleEmpty
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleFlat
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Assembly
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.LowCycleCensusNormalization
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TranslationNormalization

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask MiddleFloorData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The logical representative numbering agrees with the low-cycle normalization table. -/
theorem lowRepresentative_empty : ∀ i : Fin 38,
    LowCycleNormalization.repAt i = emptyBeta i := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The stabilizer representative numbering agrees with the low-cycle normalization table. -/
theorem lowRepresentative_flat : ∀ i : Fin 7,
    LowCycleNormalization.repAt (38 + i.val) = flatBeta i := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light middle cycle with nonzero bottom shadow is a boundary. -/
theorem middle_light_nonzero_boundary {v : MiddleGroup × Fin 2 → ZMod 2}
    (hv : v ∈ middleComplex.cycles) (hw : middleComplex.chainWeight v ≤ 10)
    (hne : baseCover.push1 v ≠ 0) : v ∈ middleComplex.boundaries := by
  by_contra hn
  have hcycles := baseCover.push1_mem_cycles hv
  have hweight : baseComplex.chainWeight (baseCover.push1 v) ≤ 10 :=
    (baseCover.chainWeight_push_le v).trans hw
  have hcensus := base_cycle_mem_census hcycles hweight
  rcases LowCycleNormalization.normalize_census (baseCover.push1 v) hcensus with hz | ⟨j, g, hj⟩
  · exact hne hz
  let w := translate1 (baseSection g) v
  have hwcycle : w ∈ middleComplex.cycles := translate1_mem_cycles _ hv
  have hwnonboundary : w ∉ middleComplex.boundaries := translate1_not_boundary _ hn
  have hwsmall : middleComplex.chainWeight w ≤ 10 := by
    change (bbChainComplex middleA middleB).chainWeight (translate1 (baseSection g) v) ≤ 10
    rw [chainWeight_translate1]
    exact hw
  have hshadow : maskOf baseQubitEnum (baseCover.push1 w) = LowCycleNormalization.repAt j := by
    change maskOf baseQubitEnum (baseCover.push1 (translate1 (baseSection g) v)) = _
    rw [baseCover.push1_translate1]
    change maskOf baseQubitEnum (translate1 (baseProjection (baseSection g)) (baseCover.push1 v)) = _
    rw [baseProjection_section]
    exact hj
  by_cases he : j.val < 38
  · let i : Fin 38 := ⟨j.val, he⟩
    have hi : LowCycleNormalization.repAt j = emptyBeta i := lowRepresentative_empty i
    exact middle_empty_shadow_impossible hwcycle hwsmall i (hshadow.trans hi)
  · let i : Fin 7 := ⟨j.val - 38, by omega⟩
    have hij : 38 + i.val = j.val := by dsimp [i]; omega
    have hi : LowCycleNormalization.repAt j = flatBeta i := by
      rw [← hij]
      exact lowRepresentative_flat i
    exact hwnonboundary (middle_flat_shadow_boundary base_logical_floor hwcycle hwsmall i
      (hshadow.trans hi))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The middle quotient has logical weight at least twelve. -/
theorem middle_logical_floor : topCover.LogicalFloor 12 :=
  middle_floor_of_certificates base_logical_floor
    (fun _ hv hw hn => middle_light_nonzero_boundary hv hw hn)

end Quantum.Stabilizer.Homological.BB.Bravyi360

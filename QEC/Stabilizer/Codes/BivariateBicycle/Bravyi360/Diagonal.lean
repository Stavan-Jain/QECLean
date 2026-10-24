import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DiagonalEmpty
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DiagonalFlat

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Pulling the last thirty-six logical representatives to the middle layer gives
exactly the shadows excluded by the overflow-one dual certificates. -/
theorem diagonalRepresentative_empty : ∀ i : Fin 36,
    maskOf middleQubitEnum (baseCover.pull1
      (chainOfMask baseQubitEnum (LowCycleNormalization.repAt (i.val + 2)))) =
        DiagonalData.emptyBeta i := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Pulling the seven stabilizer representatives gives the certified flat shadows. -/
theorem diagonalRepresentative_flat : ∀ i : Fin 7,
    maskOf middleQubitEnum (baseCover.pull1
      (chainOfMask baseQubitEnum (LowCycleNormalization.repAt (38 + i.val)))) =
        DiagonalData.flatBeta i := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The two deeper logical fibers, the thirty-six small dual obstructions, and
seven flat boundaries exhaust every nonzero light diagonal shadow. -/
theorem diagonal_light_boundary
    (hfirst : ∀ i : Fin 2, ∀ v : Group × Fin 2 → ZMod 2,
      v ∈ complex.cycles → complex.chainWeight v ≤ 22 →
      topCover.push1 v = baseCover.pull1
        (chainOfMask baseQubitEnum (LowCycleNormalization.repAt i.val)) → False)
    (u : BaseGroup × Fin 2 → ZMod 2) (hu : u ∈ baseComplex.cycles)
    (huw : baseComplex.chainWeight u ≤ 10) (hne : u ≠ 0)
    (v : Group × Fin 2 → ZMod 2) (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22) (hpush : topCover.push1 v = baseCover.pull1 u) :
    v ∈ complex.boundaries := by
  by_contra hn
  rcases LowCycleNormalization.normalize_census u (base_cycle_mem_census hu huw) with
    hz | ⟨j, g, hj⟩
  · exact hne hz
  let w := translate1 (liftTranslation g) v
  have hwcycle : w ∈ complex.cycles := translate1_mem_cycles _ hv
  have hwnonboundary : w ∉ complex.boundaries := translate1_not_boundary _ hn
  have hwsmall : complex.chainWeight w ≤ 22 := by
    change (bbChainComplex A B).chainWeight (translate1 (liftTranslation g) v) ≤ 22
    rw [chainWeight_translate1]
    exact hw
  have hgamma : translate1 g u = chainOfMask baseQubitEnum (LowCycleNormalization.repAt j) := by
    rw [← hj, chainOfMask_maskOf]
  have hshadow : topCover.push1 w = baseCover.pull1
      (chainOfMask baseQubitEnum (LowCycleNormalization.repAt j)) := by
    exact (top_push_diagonal_translate g v u hpush).trans (congrArg baseCover.pull1 hgamma)
  by_cases hsmall : j.val < 2
  · exact hfirst ⟨j.val, hsmall⟩ w hwcycle hwsmall hshadow
  by_cases hlogical : j.val < 38
  · let i : Fin 36 := ⟨j.val - 2, by omega⟩
    have hij : i.val + 2 = j.val := by dsimp [i]; omega
    apply diagonal_empty_shadow_impossible hwcycle hwsmall i
    rw [hshadow, ← hij]
    exact diagonalRepresentative_empty i
  · let i : Fin 7 := ⟨j.val - 38, by omega⟩
    have hij : 38 + i.val = j.val := by dsimp [i]; omega
    apply hwnonboundary
    apply diagonal_flat_shadow_boundary middle_logical_floor hwcycle hwsmall i
    rw [hshadow, ← hij]
    exact diagonalRepresentative_flat i

end Quantum.Stabilizer.Homological.BB.Bravyi360

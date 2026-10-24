import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Reachability
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBank
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TranslationNormalization
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchData

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A complete bottom orbit census, complete middle fibers, and the top-bank
boundary classification exclude every light cycle with nonzero bottom shadow. -/
theorem nonzero_shadow_boundary_of_bank
    (normalize : ∀ u : BaseGroup × Fin 2 → ZMod 2,
      XorSpan (ReachabilityData.reachableGenerators.map Prod.snd) (maskOf baseQubitEnum u) →
      baseComplex.chainWeight u ≤ 22 →
      ∃ (i : Fin 274011) (g : BaseGroup),
        maskOf baseQubitEnum (translate1 g u) = OrbitBatchData.repAt i)
    (bottomComplete : ∀ i : Fin 274011, ∀ u : MiddleGroup × Fin 2 → ZMod 2,
      u ∈ middleComplex.cycles → middleComplex.chainWeight u ≤ 22 →
      maskOf baseQubitEnum (baseCover.push1 u) = OrbitBatchData.repAt i →
      OrbitBatchData.repAt i ≠ 0 →
      ∃ (g : BaseGroup) (j : Fin 58130),
        maskOf middleQubitEnum (translate1 (baseSection g) u) = topBankMask j ∨
          maskOf middleQubitEnum (baseCover.deckShift1 (translate1 (baseSection g) u)) = topBankMask j)
    (topComplete : ∀ j : Fin 58130, ∀ v : Group × Fin 2 → ZMod 2,
      v ∈ complex.cycles → complex.chainWeight v ≤ 22 →
      maskOf middleQubitEnum (topCover.push1 v) = topBankMask j →
      v ∈ complex.boundaries)
    (v : Group × Fin 2 → ZMod 2) (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22)
    (hne : baseCover.push1 (topCover.push1 v) ≠ 0) : v ∈ complex.boundaries := by
  by_contra hn
  let u := baseCover.push1 (topCover.push1 v)
  have huw : baseComplex.chainWeight u ≤ 22 :=
    (baseCover.chainWeight_push_le _).trans ((topCover.chainWeight_push_le v).trans hw)
  obtain ⟨i,g,hg⟩ := normalize u (bottomShadow_mem_reachable hv) huw
  have hi : OrbitBatchData.repAt i ≠ 0 := by
    intro hz
    have ht : translate1 g u = 0 := by
      apply maskOf_injective baseQubitEnum
      exact hg.trans (hz.trans (maskOf_zero baseQubitEnum).symm)
    have hu := congrArg (translate1 (-g)) ht
    rw [translate1_neg_cancel] at hu
    exact hne hu
  let w := translate1 (liftTranslation g) v
  have hcw : w ∈ complex.cycles := translate1_mem_cycles _ hv
  have hnw : w ∉ complex.boundaries := translate1_not_boundary _ hn
  have hww : complex.chainWeight w ≤ 22 := by
    change (bbChainComplex A B).chainWeight (translate1 (liftTranslation g) v) ≤ 22
    rw [chainWeight_translate1]
    exact hw
  have hshadow : maskOf baseQubitEnum (baseCover.push1 (topCover.push1 w)) =
      OrbitBatchData.repAt i := by
    change maskOf baseQubitEnum
      (baseCover.push1 (topCover.push1 (translate1 (liftTranslation g) v))) = _
    rw [push_push_translate1]
    exact hg
  obtain ⟨h, j, hj⟩ := bottomComplete i (topCover.push1 w)
    (topCover.push1_mem_cycles hcw) ((topCover.chainWeight_push_le w).trans hww) hshadow hi
  let z := translate1 (liftTranslation h) w
  have hcz : z ∈ complex.cycles := translate1_mem_cycles _ hcw
  have hnz : z ∉ complex.boundaries := translate1_not_boundary _ hnw
  have hwz : complex.chainWeight z ≤ 22 := by
    change (bbChainComplex A B).chainWeight (translate1 (liftTranslation h) w) ≤ 22
    rw [chainWeight_translate1]
    exact hww
  have hz : topCover.push1 z = translate1 (baseSection h) (topCover.push1 w) := by
    rw [topCover.push1_translate1]
    change translate1 (topProjection (topSection (baseSection h))) _ = _
    rw [topProjection_section]
  rcases hj with hj | hj
  · exact hnz (topComplete j z hcz hwz (by rw [hz]; exact hj))
  · let t := translate1 (15,0) z
    have hct : t ∈ complex.cycles := translate1_mem_cycles _ hcz
    have hnt : t ∉ complex.boundaries := translate1_not_boundary _ hnz
    have hwt : complex.chainWeight t ≤ 22 := by
      change (bbChainComplex A B).chainWeight (translate1 (15,0) z) ≤ 22
      rw [chainWeight_translate1]
      exact hwz
    apply hnt
    apply topComplete j t hct hwt
    change maskOf middleQubitEnum (topCover.push1 (translate1 (15,0) z)) = _
    rw [top_push_horizontal_translation, hz]
    exact hj

end Quantum.Stabilizer.Homological.BB.Bravyi360

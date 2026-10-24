import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomCaseChecks
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Fibers
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeckJoin
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBank
import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepNormalization

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shallow packed fibers and the twenty-eight deep physical fibers exhaust
all nonzero projected cycles in the orbit census. -/
theorem bottom_complete_of_families
    (shallow : ∀ i : Fin 274011, BottomCase.tag i ≠ 5 → OrbitBatchData.repAt i ≠ 0 →
      ∀ a : Nat, a < 2 ^ 90 →
      reconX bottomEColumns a = reconX bottomRColumns (OrbitBatchData.repAt i) →
      bitCount 90 (outsideMask a (OrbitBatchData.repAt i)) ≤
        (22 - bitCount 90 (OrbitBatchData.repAt i)) / 2 →
      ∃ j : Fin 58130,
        bottomJoin a (OrbitBatchData.repAt i) = topBankMask j ∨
        bottomJoin (a ^^^ OrbitBatchData.repAt i) (OrbitBatchData.repAt i) = topBankMask j)
    (deep : ∀ i : Fin 28, ∀ u : MiddleGroup × Fin 2 → ZMod 2,
      u ∈ middleComplex.cycles → middleComplex.chainWeight u ≤ 22 →
      maskOf baseQubitEnum (baseCover.push1 u) = DeepFiberData.betaAt i →
      ∃ j : Fin 58130, maskOf middleQubitEnum u = topBankMask j ∨
        maskOf middleQubitEnum (baseCover.deckShift1 u) = topBankMask j)
    (i : Fin 274011) (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hshadow : maskOf baseQubitEnum (baseCover.push1 u) = OrbitBatchData.repAt i)
    (hne : OrbitBatchData.repAt i ≠ 0) :
    ∃ (g : BaseGroup) (j : Fin 58130),
      maskOf middleQubitEnum (translate1 (baseSection g) u) = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 (translate1 (baseSection g) u)) = topBankMask j := by
  by_cases hd : BottomCase.tag i = 5
  · obtain ⟨hi, hb⟩ := BottomCase.deep_checked i hd
    let d : Fin 28 := ⟨BottomCase.localIndex i, hi⟩
    obtain ⟨hj, he⟩ := DeepNormalization.checked d
    let g := DeepNormalization.displacement d
    let w := translate1 (baseSection g) u
    have hcycle : w ∈ middleComplex.cycles := translate1_mem_cycles _ hu
    have hweight : middleComplex.chainWeight w ≤ 22 := by
      change (bbChainComplex middleA middleB).chainWeight (translate1 (baseSection g) u) ≤ 22
      rw [chainWeight_translate1]
      exact hw
    have hchain : chainOfMask baseQubitEnum (BottomCase.deepBeta d) = baseCover.push1 u := by
      rw [← hb, ← hshadow, chainOfMask_maskOf]
    have hbeta : maskOf baseQubitEnum (baseCover.push1 w) =
        DeepFiberData.betaAt (DeepNormalization.indexAt d) := by
      change maskOf baseQubitEnum (baseCover.push1 (translate1 (baseSection g) u)) = _
      rw [baseCover.push1_translate1]
      change maskOf baseQubitEnum (translate1 (baseProjection (baseSection g))
        (baseCover.push1 u)) = _
      rw [baseProjection_section, ← hchain]
      exact he
    obtain ⟨j, hbank⟩ := deep ⟨DeepNormalization.indexAt d, hj⟩ w hcycle hweight hbeta
    exact ⟨g, j, hbank⟩
  · obtain ⟨j, hj | hj⟩ := shallow i hd hne
      (maskOf baseQubitEnum (baseCover.sheet0 u)) (maskOf_lt _ _)
      (by rw [bottom_fiber_equation hu, hshadow]) (by
        rw [outsideMask_eq_and_complement (maskOf_lt _ _)]
        have h := baseCover.mask_overflow_le baseQubitEnum u hw
        rwa [hshadow] at h)
    · refine ⟨0, j, Or.inl ?_⟩
      have hzero : baseSection 0 = 0 := by decide +kernel
      have ht : translate1 (0 : MiddleGroup) u = u := by ext q; simp [translate1]
      rw [hzero, ht]
      rw [maskOf_middle_eq_join, hshadow]
      exact hj
    · refine ⟨0, j, Or.inr ?_⟩
      have hzero : baseSection 0 = 0 := by decide +kernel
      have ht : translate1 (0 : MiddleGroup) u = u := by ext q; simp [translate1]
      rw [hzero, ht]
      rw [maskOf_middle_deck_eq_join, hshadow]
      exact hj

end Quantum.Stabilizer.Homological.BB.Bravyi360

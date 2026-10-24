import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCaseChecks
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFlat
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBridge

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData TopCaseData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The six certified families cover every top-bank shadow, including all empty fibers. -/
theorem topBank_boundary_of_families (hmiddle : topCover.LogicalFloor 12)
    (hnonempty : ∀ i : Fin 649, TopFiberBoundary (nonemptyBeta i))
    (hexception : ∀ i : Fin 4, ∀ word, word < 2 ^ 180 →
      reconX topEColumns word = reconX topRColumns (exceptionalBeta i) →
      bitCount 180 (outsideMask word (exceptionalBeta i)) ≤ 3 → False)
    (hempty0 : ∀ i : Fin 24877, ∀ word, word < 2 ^ 180 →
      reconX topEColumns word = reconX topRColumns (TopEmpty.beta0 i) →
      bitCount 180 (outsideMask word (TopEmpty.beta0 i)) ≤ 0 → False)
    (hempty1 : ∀ i : Fin 2119, ∀ word, word < 2 ^ 180 →
      reconX topEColumns word = reconX topRColumns (TopEmpty.beta1 i) →
      bitCount 180 (outsideMask word (TopEmpty.beta1 i)) ≤ 1 → False)
    (hempty2 : ∀ i : Fin 143, ∀ word, word < 2 ^ 180 →
      reconX topEColumns word = reconX topRColumns (TopEmpty.beta2 i) →
      bitCount 180 (outsideMask word (TopEmpty.beta2 i)) ≤ 2 → False)
    (i : Fin 58130) {v : Group × Fin 2 → ZMod 2} (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22)
    (hshadow : maskOf middleQubitEnum (topCover.push1 v) = topBankMask i) :
    v ∈ complex.boundaries := by
  have h := TopCaseData.all_checked i
  dsimp only [Valid] at h
  have hf : tagAt i % 8 = 0 ∨ tagAt i % 8 = 1 ∨ tagAt i % 8 = 2 ∨
      tagAt i % 8 = 3 ∨ tagAt i % 8 = 4 ∨ tagAt i % 8 = 5 := by omega
  rcases hf with hf | hf | hf | hf | hf | hf
  · simp only [hf, familySize, familyBeta, familyCap] at h
    exact topFlat_boundary hmiddle ⟨tagAt i / 8, h.2.1⟩ hv hw (hshadow.trans h.2.2.1)
  · simp only [hf, familySize, familyBeta, familyCap] at h
    exact topFiberBoundary_apply (hnonempty ⟨tagAt i / 8, h.2.1⟩) hv hw (hshadow.trans h.2.2.1)
  · simp only [hf, familySize, familyBeta, familyCap] at h
    exfalso
    apply topFiberEmpty_apply (hexception ⟨tagAt i / 8, h.2.1⟩) ?_ hv hw
      (hshadow.trans h.2.2.1)
    have hc := h.2.2.2 (by decide)
    rw [fast180_eq, h.2.2.1] at hc
    exact hc
  · simp only [hf, familySize, familyBeta, familyCap] at h
    exfalso
    apply topFiberEmpty_apply (hempty0 ⟨tagAt i / 8, h.2.1⟩) ?_ hv hw
      (hshadow.trans h.2.2.1)
    have hc := h.2.2.2 (by decide)
    rw [fast180_eq, h.2.2.1] at hc
    exact hc
  · simp only [hf, familySize, familyBeta, familyCap] at h
    exfalso
    apply topFiberEmpty_apply (hempty1 ⟨tagAt i / 8, h.2.1⟩) ?_ hv hw
      (hshadow.trans h.2.2.1)
    have hc := h.2.2.2 (by decide)
    rw [fast180_eq, h.2.2.1] at hc
    exact hc
  · simp only [hf, familySize, familyBeta, familyCap] at h
    exfalso
    apply topFiberEmpty_apply (hempty2 ⟨tagAt i / 8, h.2.1⟩) ?_ hv hw
      (hshadow.trans h.2.2.1)
    have hc := h.2.2.2 (by decide)
    rw [fast180_eq, h.2.2.1] at hc
    exact hc

end Quantum.Stabilizer.Homological.BB.Bravyi360

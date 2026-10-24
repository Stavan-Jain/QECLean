import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowLinks
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmpty2
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomEmptyWeights

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
open F2Mask FiberData
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact family association reduces every nonzero shallow representative to its positive forest. -/
theorem bottomFiber_complete_of_forest
    (hforest : ∀ (j : Fin 27867) (word : Nat), word < 2^90 →
      reconX bottomEColumns word = reconX bottomRColumns (BottomForest.fiberAt j.val).beta →
      bitCount 90 (outsideMask word (BottomForest.fiberAt j.val).beta) ≤
        (22-bitCount 90 (BottomForest.fiberAt j.val).beta)/2 →
      ∃ k : Fin 58130, bottomJoin word (BottomForest.fiberAt j.val).beta = topBankMask k ∨
        bottomJoin (word ^^^ (BottomForest.fiberAt j.val).beta)
          (BottomForest.fiberAt j.val).beta = topBankMask k)
    (i : Fin 274011) (hdeep : BottomCase.tag i.val ≠ 5)
    (hnonzero : OrbitBatchData.repAt i.val ≠ 0)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns (OrbitBatchData.repAt i.val))
    (hoff : bitCount 90 (outsideMask word (OrbitBatchData.repAt i.val)) ≤
      (22-bitCount 90 (OrbitBatchData.repAt i.val))/2) :
    ∃ k : Fin 58130, bottomJoin word (OrbitBatchData.repAt i.val) = topBankMask k ∨
      bottomJoin (word ^^^ OrbitBatchData.repAt i.val) (OrbitBatchData.repAt i.val) = topBankMask k := by
  rcases linkCheck_sound i.val (link_checked i) with
    ⟨_,hj,hb⟩ | ⟨_,hj,hb⟩ | ⟨_,hj,hb⟩ | ⟨_,hj,hb⟩ | ⟨_,hb⟩ | hd
  · let j : Fin 224352 := ⟨BottomCase.localIndex i.val,hj⟩
    have he' : reconX bottomEColumns word = reconX bottomRColumns (BottomEmpty.beta0 j.val) := by simpa only [j,hb] using he
    have ho : bitCount 90 (outsideMask word (BottomEmpty.beta0 j.val)) ≤ 0 := by
      rw [hb,BottomEmpty.beta0_weight j] at hoff
      exact hoff
    exact False.elim (BottomEmpty.cap0_impossible j word hw he' ho)
  · let j : Fin 20904 := ⟨BottomCase.localIndex i.val,hj⟩
    have he' : reconX bottomEColumns word = reconX bottomRColumns (BottomEmpty.beta1 j.val) := by simpa only [j,hb] using he
    have ho : bitCount 90 (outsideMask word (BottomEmpty.beta1 j.val)) ≤ 1 := by
      rw [hb,BottomEmpty.beta1_weight j] at hoff
      exact hoff
    exact False.elim (BottomEmpty.cap1_impossible j word hw he' ho)
  · let j : Fin 859 := ⟨BottomCase.localIndex i.val,hj⟩
    have he' : reconX bottomEColumns word = reconX bottomRColumns (BottomEmpty.beta2 j.val) := by simpa only [j,hb] using he
    have ho : bitCount 90 (outsideMask word (BottomEmpty.beta2 j.val)) ≤ 2 := by
      rw [hb,BottomEmpty.beta2_weight j] at hoff
      exact hoff
    exact False.elim (BottomEmpty.cap2_impossible j word hw he' ho)
  · rw [hb] at he hoff ⊢
    exact hforest ⟨BottomCase.localIndex i.val,hj⟩ word hw he hoff
  · exact False.elim (hnonzero hb)
  · exact False.elim (hdeep hd)

#print axioms bottomFiber_complete_of_forest
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow

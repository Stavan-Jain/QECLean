import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveOne
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveTwo
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchComplete

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every actual low-weight solution above a positive shallow shadow reaches the common top bank. -/
theorem positiveFiber_complete (j : Fin 27867) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns (fiberAt j.val).beta)
    (hoff : bitCount 90 (outsideMask word (fiberAt j.val).beta) ≤
      (22-bitCount 90 (fiberAt j.val).beta)/2) :
    ∃ k : Fin 58130, bottomJoin word (fiberAt j.val).beta = topBankMask k ∨
      bottomJoin (word ^^^ (fiberAt j.val).beta) (fiberAt j.val).beta = topBankMask k := by
  apply fiberAt_complete j word he
  have hb := fiberCheck_weight _ (fiberAt_checked j)
  have ho : bitCount 90 (outsideMask word (fiberAt j.val).beta) ≤ outsideBudget (fiberAt j.val) := by
    simpa only [outsideBudget,hb] using hoff
  have hs := fiberAt_weights j
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with h | h | h | h | h
  · exact highFiberAt_complete j (Or.inr h) word hw he ho
  · exact highFiberAt_complete j (Or.inl h) word hw he ho
  · apply twoFiberAt_complete j h word hw he
    simpa only [outsideBudget,h] using ho
  · apply oneFiberAt_complete j h word hw he
    simpa only [outsideBudget,h] using ho
  · apply zeroFiberAt_complete j h word hw
    simpa only [outsideBudget,h] using ho

#print axioms positiveFiber_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest

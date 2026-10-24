import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallowAssembly
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomPositiveComplete

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow
open F2Mask FiberData
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every nonzero, non-deep canonical shadow has its complete actual fiber
in the common top bank. -/
theorem bottomFiber_complete (i : Fin 274011) (hdeep : BottomCase.tag i.val ≠ 5)
    (hnonzero : OrbitBatchData.repAt i.val ≠ 0)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns (OrbitBatchData.repAt i.val))
    (hoff : bitCount 90 (outsideMask word (OrbitBatchData.repAt i.val)) ≤
      (22-bitCount 90 (OrbitBatchData.repAt i.val))/2) :
    ∃ k : Fin 58130, bottomJoin word (OrbitBatchData.repAt i.val) = topBankMask k ∨
      bottomJoin (word ^^^ OrbitBatchData.repAt i.val) (OrbitBatchData.repAt i.val) = topBankMask k :=
  bottomFiber_complete_of_forest BottomForest.positiveFiber_complete i hdeep hnonzero word hw he hoff

#print axioms bottomFiber_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomShallow

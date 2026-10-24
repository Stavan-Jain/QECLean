import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomFiberBridge
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomShallow
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFiberComplete

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask

/-- Every light middle cycle over a nonzero reachable orbit representative reaches
the common top bank after a base translation and, if needed, a deck exchange. -/
theorem bottom_complete (i : Fin 274011) (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hshadow : maskOf baseQubitEnum (baseCover.push1 u) = OrbitBatchData.repAt i)
    (hne : OrbitBatchData.repAt i ≠ 0) :
    ∃ (g : BaseGroup) (j : Fin 58130),
      maskOf middleQubitEnum (translate1 (baseSection g) u) = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 (translate1 (baseSection g) u)) = topBankMask j := by
  exact bottom_complete_of_families BottomShallow.bottomFiber_complete deepFiber_complete i u hu hw hshadow hne

#print axioms bottom_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360

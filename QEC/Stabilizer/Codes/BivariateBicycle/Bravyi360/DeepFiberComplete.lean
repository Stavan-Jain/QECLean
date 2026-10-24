import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFlatComplete
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepExceptionalBridge
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFiberData

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The common deep-family order agrees with the twenty-six flat certificate shadows. -/
theorem deepFiber_flat_indices : ∀ i : Fin 26,
    DeepFiberData.betaAt i = DeepFlatData.betaAt i := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- All twenty-eight deep middle fibers reach the top bank after at most a deck exchange. -/
theorem deepFiber_complete (i : Fin 28) (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hb : maskOf baseQubitEnum (baseCover.push1 u) = DeepFiberData.betaAt i) :
    ∃ j : Fin 58130, maskOf middleQubitEnum u = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 u) = topBankMask j := by
  by_cases hi : i.val < 26
  · exact deep_flat_complete ⟨i.val, hi⟩ u hu hw (hb.trans (deepFiber_flat_indices ⟨i.val, hi⟩))
  · have hi' : i.val = 26 ∨ i.val = 27 := by omega
    rcases hi' with hi' | hi'
    · have h := deep_exceptional_complete0 u hu hw
      apply h
      simpa only [hi', show DeepFiberData.betaAt 26 = 0x7008000c00001200200049 by decide +kernel] using hb
    · have h := deep_exceptional_complete1 u hu hw
      apply h
      simpa only [hi', show DeepFiberData.betaAt 27 = 0x100020004018007000e001 by decide +kernel] using hb

#print axioms deepFiber_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360

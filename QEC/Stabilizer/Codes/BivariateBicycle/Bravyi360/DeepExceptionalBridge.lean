import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepBank
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeckJoin
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Fibers

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask

/--
A complete packed middle fiber gives the same physical bank membership
statement.
-/
theorem physical_deep_of_packed (beta : Nat) (hwt : bitCount 90 beta = 12)
    (complete : ∀ a : Nat, a < 2^90 →
      reconX FiberData.bottomEColumns a = reconX FiberData.bottomRColumns beta →
      bitCount 90 (outsideMask a beta) ≤ 5 →
      ∃ j : Fin 58130, bottomJoin a beta = topBankMask j ∨
        bottomJoin (a ^^^ beta) beta = topBankMask j)
    (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hb : maskOf baseQubitEnum (baseCover.push1 u) = beta) :
    ∃ j : Fin 58130, maskOf middleQubitEnum u = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 u) = topBankMask j := by
  obtain ⟨j, hj⟩ := complete (maskOf baseQubitEnum (baseCover.sheet0 u)) (maskOf_lt _ _)
    (by rw [bottom_fiber_equation hu, hb]) (by
      rw [outsideMask_eq_and_complement (maskOf_lt _ _)]
      have h := baseCover.mask_overflow_le baseQubitEnum u hw
      rwa [hb, hwt] at h)
  refine ⟨j, ?_⟩
  rw [maskOf_middle_eq_join, maskOf_middle_deck_eq_join, hb]
  exact hj

/--
Every light middle cycle above the first cap-five shadow reaches the top bank
up to deck action.
-/
theorem deep_exceptional_complete0 (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hb : maskOf baseQubitEnum (baseCover.push1 u) = 0x7008000c00001200200049) :
    ∃ j : Fin 58130, maskOf middleQubitEnum u = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 u) = topBankMask j :=
  physical_deep_of_packed _ (by decide +kernel)
    (fun _ ha he hw => DeepBank.complete0 ha he hw) u hu hw hb

/--
Every light middle cycle above the second cap-five shadow reaches the top bank
up to deck action.
-/
theorem deep_exceptional_complete1 (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hb : maskOf baseQubitEnum (baseCover.push1 u) = 0x100020004018007000e001) :
    ∃ j : Fin 58130, maskOf middleQubitEnum u = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 u) = topBankMask j :=
  physical_deep_of_packed _ (by decide +kernel)
    (fun _ ha he hw => DeepBank.complete1 ha he hw) u hu hw hb

#print axioms deep_exceptional_complete0
#print axioms deep_exceptional_complete1
end Quantum.Stabilizer.Homological.BB.Bravyi360

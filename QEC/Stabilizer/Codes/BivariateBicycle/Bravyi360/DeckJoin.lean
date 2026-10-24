import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Join

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask

/-- The bottom deck involution preserves the projected shadow. -/
theorem bottom_push_deck (u : MiddleGroup × Fin 2 → ZMod 2) :
    baseCover.push1 (baseCover.deckShift1 u) = baseCover.push1 u := by
  rw [← baseCover.sheets_add_eq_push, baseCover.sheet0_deckShift1,
    baseCover.sheet1_deckShift1, add_comm, baseCover.sheets_add_eq_push]

/-- Reading the deck-translated middle chain exchanges its two packed sheets. -/
theorem maskOf_middle_deck_eq_join (u : MiddleGroup × Fin 2 → ZMod 2) :
    maskOf middleQubitEnum (baseCover.deckShift1 u) =
      bottomJoin (maskOf baseQubitEnum (baseCover.sheet0 u) ^^^
        maskOf baseQubitEnum (baseCover.push1 u))
        (maskOf baseQubitEnum (baseCover.push1 u)) := by
  rw [maskOf_middle_eq_join, bottom_push_deck, baseCover.sheet0_deckShift1,
    baseCover.sheet1_eq_sheet0_add_push, maskOf_add]

end Quantum.Stabilizer.Homological.BB.Bravyi360

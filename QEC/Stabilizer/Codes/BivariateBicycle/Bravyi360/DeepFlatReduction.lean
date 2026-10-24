import QEC.Stabilizer.Framework.Homological.BBFlatLift
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BaseFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.LowCycleCensusNormalization
import QEC.Stabilizer.Framework.Homological.Certificate.MaskJoin

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask

/-- A light lift of a flat middle boundary has a sheet listed by the complete base-cycle census,
up to adding its shadow (the deck action). -/
theorem flat_sheet_mem_base_census {c v : MiddleGroup × Fin 2 → ZMod 2}
    (hc : c ∈ middleComplex.boundaries)
    (hflat : ∀ q, baseCover.sheet0 c q ≠ 0 → baseCover.push1 c q ≠ 0)
    (hv : v ∈ middleComplex.cycles) (hpush : baseCover.push1 v = baseCover.push1 c)
    (hweight : middleComplex.chainWeight v ≤ 22) :
    ∃ j : Fin 1954,
      maskOf baseQubitEnum (baseCover.sheet0 v) =
        maskOf baseQubitEnum (baseCover.sheet0 c) ^^^ LowCycleNormalization.maskAt j.val ∨
      maskOf baseQubitEnum (baseCover.sheet0 v) =
        maskOf baseQubitEnum (baseCover.sheet0 c) ^^^ LowCycleNormalization.maskAt j.val ^^^
          maskOf baseQubitEnum (baseCover.push1 c) := by
  obtain ⟨u, hu, hw, hrelation⟩ := baseCover.exists_light_cycle_of_flat_boundary
    (w := 11) hc hflat hv hpush (by change middleComplex.chainWeight v ≤ 23; omega)
  have hw10 : baseComplex.chainWeight u ≤ 10 := by
    obtain ⟨t, ht⟩ := base_cycle_even hu
    change baseComplex.chainWeight u ≤ 11 at hw
    omega
  have hm := base_cycle_mem_census hu hw10
  rw [← LowCycleNormalization.census_indices, List.mem_ofFn] at hm
  obtain ⟨j, hj⟩ := hm
  refine ⟨j, ?_⟩
  have cancel (a b : Nat) : a ^^^ b ^^^ b = a := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rcases hrelation with h | h
  · left
    have hs := congrArg (fun w => maskOf baseQubitEnum (baseCover.sheet0 w)) h
    dsimp only at hs
    rw [baseCover.sheet0_add, baseCover.sheet0_pull1, maskOf_add, ← hj] at hs
    have he := congrArg (fun x => x ^^^ maskOf baseQubitEnum (baseCover.sheet0 c)) hs
    dsimp only at he
    rw [cancel] at he
    exact he.trans (Nat.xor_comm _ _)
  · right
    have hs := congrArg (fun w => maskOf baseQubitEnum (baseCover.sheet0 w)) h
    dsimp only at hs
    rw [baseCover.sheet0_add, baseCover.sheet0_pull1, maskOf_add,
      baseCover.sheet0_deckShift1, baseCover.sheet1_eq_sheet0_add_push, maskOf_add,
      hpush, ← hj] at hs
    have he := congrArg (fun x => x ^^^ maskOf baseQubitEnum (baseCover.sheet0 c) ^^^
      maskOf baseQubitEnum (baseCover.push1 c)) hs
    dsimp only at he
    rw [cancel, cancel] at he
    exact he.trans (congrArg (fun x => x ^^^ maskOf baseQubitEnum (baseCover.push1 c))
      (Nat.xor_comm _ _))

#print axioms flat_sheet_mem_base_census
end Quantum.Stabilizer.Homological.BB.Bravyi360

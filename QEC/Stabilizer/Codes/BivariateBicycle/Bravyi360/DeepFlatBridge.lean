import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFlatReduction
import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomBoundarySheets
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFlatData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeckJoin

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adding the shadow exchanges sheets without changing their off-shadow support. -/
theorem outsideMask_xor_shadow (a b : Nat) : outsideMask (a ^^^ b) b = outsideMask a b := by
  simp only [outsideMask, Nat.and_xor_distrib_right, Nat.and_self]
  calc
    (a ^^^ b) ^^^ ((a &&& b) ^^^ b) = (a ^^^ (a &&& b)) ^^^ (b ^^^ b) := by ac_rfl
    _ = a ^^^ (a &&& b) := by rw [Nat.xor_self, Nat.xor_zero]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A tagged join certificate chooses one of the two deck-equivalent sheets. -/
theorem bank_case_of_tag (a b t : Nat)
    (h : 22 < DeepFlatData.fast90 b + 2 * DeepFlatData.fast90 (a &&& ((2^90-1) ^^^ b)) ∨
      (t/2 < topBankSize ∧ bottomJoin (if t%2=1 then a ^^^ b else a) b = topBankMask (t/2))) :
    22 < bitCount 90 b + 2 * bitCount 90 (a &&& ((2^90-1) ^^^ b)) ∨
      ∃ j : Fin 58130, bottomJoin a b = topBankMask j ∨ bottomJoin (a ^^^ b) b = topBankMask j := by
  rcases h with h | h
  · left
    simpa only [DeepFlatData.fast90_eq] using h
  · right
    refine ⟨⟨t/2, h.1⟩, ?_⟩
    by_cases ht : t%2=1
    · exact Or.inr (by simpa only [if_pos ht] using h.2)
    · exact Or.inl (by simpa only [if_neg ht] using h.2)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The twenty-six particular lifts are explicit flat physical boundaries. -/
theorem deep_flat_matrices_checked : ∀ i : Fin 26,
    DeepFlatData.coeffAt i < 2^90 ∧
    reconX DeepFlatData.sheetColumns (DeepFlatData.coeffAt i) = DeepFlatData.firstAt i ∧
    reconX DeepFlatData.shadowColumns (DeepFlatData.coeffAt i) = DeepFlatData.betaAt i ∧
    DeepFlatData.firstAt i &&& ((2^90-1) ^^^ DeepFlatData.betaAt i) = 0 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exchanging sheets preserves the property of joining to a specified bank member. -/
theorem join_bank_of_sheet_choice {a b s : Nat}
    (hs : s = a ∨ s = a ^^^ b)
    (h : ∃ j : Fin 58130, bottomJoin a b = topBankMask j ∨
      bottomJoin (a ^^^ b) b = topBankMask j) :
    ∃ j : Fin 58130, bottomJoin s b = topBankMask j ∨
      bottomJoin (s ^^^ b) b = topBankMask j := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  rcases hs with rfl | rfl
  · exact hj
  · rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    exact hj.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light middle cycle over one of the twenty-six flat deep shadows lies in the top bank,
possibly after exchanging its sheets. -/
theorem deep_flat_complete_of_census (hchecked : ∀ i : Fin 26, ∀ j : Fin 1954,
      let a := DeepFlatData.firstAt i ^^^ LowCycleNormalization.maskAt j
      let b := DeepFlatData.betaAt i
      22 < bitCount 90 b + 2 * bitCount 90 (a &&& ((2^90-1) ^^^ b)) ∨
        ∃ k : Fin 58130, bottomJoin a b = topBankMask k ∨ bottomJoin (a ^^^ b) b = topBankMask k)
    (i : Fin 26) (u : MiddleGroup × Fin 2 → ZMod 2)
    (hu : u ∈ middleComplex.cycles) (hw : middleComplex.chainWeight u ≤ 22)
    (hb : maskOf baseQubitEnum (baseCover.push1 u) = DeepFlatData.betaAt i) :
    ∃ j : Fin 58130, maskOf middleQubitEnum u = topBankMask j ∨
      maskOf middleQubitEnum (baseCover.deckShift1 u) = topBankMask j := by
  let c := middleComplex.boundary2 (chainOfMask middleFaceEnum (DeepFlatData.coeffAt i))
  have hc : c ∈ middleComplex.boundaries := ⟨_, rfl⟩
  have hd := deep_flat_matrices_checked i
  have hfirst : maskOf baseQubitEnum (baseCover.sheet0 c) = DeepFlatData.firstAt i :=
    (bottomBoundarySheet_mask _ hd.1).trans hd.2.1
  have hshadow : maskOf baseQubitEnum (baseCover.push1 c) = DeepFlatData.betaAt i :=
    (bottomBoundaryShadow_mask _ hd.1).trans hd.2.2.1
  have hflat : ∀ q, baseCover.sheet0 c q ≠ 0 → baseCover.push1 c q ≠ 0 := by
    apply support_subset_of_mask_restrict_zero baseQubitEnum
    rw [hfirst, hshadow]
    exact hd.2.2.2
  have hpush : baseCover.push1 u = baseCover.push1 c :=
    maskOf_injective baseQubitEnum (hb.trans hshadow.symm)
  obtain ⟨j, hj⟩ := flat_sheet_mem_base_census hc hflat hu hpush hw
  rw [hfirst, hshadow] at hj
  let a := DeepFlatData.firstAt i ^^^ LowCycleNormalization.maskAt j
  let b := DeepFlatData.betaAt i
  let s := maskOf baseQubitEnum (baseCover.sheet0 u)
  have hs : s = a ∨ s = a ^^^ b := hj
  have hsb : s < 2^90 := maskOf_lt _ _
  have hbb : b < 2^90 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hab : a < 2^90 := by
    rcases hs with h | h
    · exact h ▸ hsb
    · have hx : a = s ^^^ b := by rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hx]
      exact Nat.xor_lt_two_pow hsb hbb
  have ho : outsideMask s b = outsideMask a b := by
    rcases hs with h | h
    · rw [h]
    · rw [h, outsideMask_xor_shadow]
  have hweight : bitCount 90 b + 2 * bitCount 90 (a &&& ((2^90-1) ^^^ b)) ≤ 22 := by
    have h := baseCover.weight_eq_mask_shadow_overflow baseQubitEnum u
    rw [hb, ← outsideMask_eq_and_complement hsb, ho, outsideMask_eq_and_complement hab] at h
    exact h ▸ hw
  have hbank := hchecked i j
  rcases hbank with heavy | light
  · exact False.elim (Nat.not_lt_of_ge hweight heavy)
  · obtain ⟨k, hk⟩ := join_bank_of_sheet_choice hs light
    refine ⟨k, ?_⟩
    rw [maskOf_middle_eq_join, maskOf_middle_deck_eq_join, hb]
    exact hk

#print axioms deep_flat_complete_of_census
end Quantum.Stabilizer.Homological.BB.Bravyi360

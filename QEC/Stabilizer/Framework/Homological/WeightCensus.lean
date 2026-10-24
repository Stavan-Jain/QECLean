import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis

open scoped BigOperators

/-- Reducing a generating sum modulo the first excluded weight discards precisely
the terms above that weight, provided the number of terms is smaller than the base. -/
theorem weight_sum_truncate {α : Type*} [DecidableEq α]
    (inputs : Finset α) (weight : α → Nat) (base cutoff : Nat)
    (hbase : 1 < base) (hcard : inputs.card < base) :
    (∑ a ∈ inputs, base ^ weight a) % base ^ (cutoff + 1) =
      ∑ a ∈ inputs.filter (fun a => weight a ≤ cutoff), base ^ weight a := by
  let low := inputs.filter (fun a => weight a ≤ cutoff)
  have hcongr : (∑ a ∈ inputs, base ^ weight a) ≡
      (∑ a ∈ inputs, if weight a ≤ cutoff then base ^ weight a else 0)
        [MOD base ^ (cutoff + 1)] := by
    apply Nat.ModEq.sum
    intro a ha
    split_ifs with h
    · exact Nat.ModEq.refl _
    · exact Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow base (by omega))
  have hsum : (∑ a ∈ low, base ^ weight a) ≤ low.card * base ^ cutoff := by
    calc
      _ ≤ ∑ _a ∈ low, base ^ cutoff := by
        apply Finset.sum_le_sum
        intro a ha
        exact Nat.pow_le_pow_right (by omega) (Finset.mem_filter.mp ha).2
      _ = _ := by simp
  have hlow : low.card < base := (Finset.card_filter_le _ _).trans_lt hcard
  have hlt : (∑ a ∈ low, base ^ weight a) < base ^ (cutoff + 1) := by
    rw [pow_succ']
    exact hsum.trans_lt (Nat.mul_lt_mul_of_pos_right hlow (Nat.pow_pos (by omega)))
  change _ % _ = _ % _ at hcongr
  rw [← Finset.sum_filter] at hcongr
  exact hcongr.trans (Nat.mod_eq_of_lt hlt)

/-- A packed generating sum counts low-weight inputs by two remainders:
the first removes heavy terms, and the second evaluates the remaining monomials at one. -/
theorem low_weight_count_eq_remainders {α : Type*} [DecidableEq α]
    (inputs : Finset α) (weight : α → Nat) (base cutoff : Nat)
    (hbase : 1 < base) (hcard : inputs.card < base - 1) :
    ((∑ a ∈ inputs, base ^ weight a) % base ^ (cutoff + 1)) % (base - 1) =
      (inputs.filter (fun a => weight a ≤ cutoff)).card := by
  rw [weight_sum_truncate inputs weight base cutoff hbase (by omega)]
  have hunit : base ≡ 1 [MOD base - 1] := by
    change base % (base - 1) = 1 % (base - 1)
    have hb : base = (base - 1) + 1 := by omega
    conv_lhs => rw [hb]
    simp
  have hcongr : (∑ a ∈ inputs.filter (fun a => weight a ≤ cutoff), base ^ weight a) ≡
      (∑ _a ∈ inputs.filter (fun a => weight a ≤ cutoff), 1) [MOD base - 1] := by
    apply Nat.ModEq.sum
    intro a ha
    simpa using hunit.pow (weight a)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hcongr
  change _ % _ = _ % _ at hcongr
  exact hcongr.trans (Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt hcard))

/-- A finite target represented by an encoder has at most as many light words
as there are light inputs, even when the encoder is not injective. -/
theorem card_le_light_inputs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (inputs : Finset α) (target : Finset β) (encode : α → β)
    (weight : β → Nat) (cutoff : Nat)
    (hcover : ∀ y ∈ target, ∃ a ∈ inputs, encode a = y)
    (hlight : ∀ y ∈ target, weight y ≤ cutoff) :
    target.card ≤ (inputs.filter (fun a => weight (encode a) ≤ cutoff)).card := by
  let light := inputs.filter (fun a => weight (encode a) ≤ cutoff)
  have hsub : target ⊆ light.image encode := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hcover y hy
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hlight _ hy⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

/-- A modular generating-sum certificate bounds any light target covered by its encoder. -/
theorem card_le_of_weight_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (inputs : Finset α) (target : Finset β) (encode : α → β)
    (weight : β → Nat) (base cutoff answer : Nat)
    (hbase : 1 < base) (hcard : inputs.card < base - 1)
    (hcover : ∀ y ∈ target, ∃ a ∈ inputs, encode a = y)
    (hlight : ∀ y ∈ target, weight y ≤ cutoff)
    (hcompute : (∑ a ∈ inputs, base ^ weight (encode a)) % base ^ (cutoff + 1) = answer) :
    target.card ≤ answer % (base - 1) := by
  have hcount := low_weight_count_eq_remainders inputs (fun a => weight (encode a))
    base cutoff hbase hcard
  rw [hcompute] at hcount
  rw [hcount]
  exact card_le_light_inputs inputs target encode weight cutoff hcover hlight

/-- The same bound can consume a weighted calculation in the finite residue ring. -/
theorem card_le_of_zmod_weight_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (inputs : Finset α) (target : Finset β) (encode : α → β)
    (weight : β → Nat) (base cutoff answer : Nat)
    (hbase : 1 < base) (hcard : inputs.card < base - 1)
    (hcover : ∀ y ∈ target, ∃ a ∈ inputs, encode a = y)
    (hlight : ∀ y ∈ target, weight y ≤ cutoff)
    (hcompute : (∑ a ∈ inputs, (base : ZMod (base ^ (cutoff + 1))) ^ weight (encode a)) =
      (answer : ZMod (base ^ (cutoff + 1))))
    (hanswer : answer < base ^ (cutoff + 1)) :
    target.card ≤ answer % (base - 1) := by
  apply card_le_of_weight_sum inputs target encode weight base cutoff answer
    hbase hcard hcover hlight
  have hcast : ((∑ a ∈ inputs, base ^ weight (encode a) : Nat) : ZMod (base ^ (cutoff + 1))) =
      (answer : ZMod (base ^ (cutoff + 1))) := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using hcompute
  have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  exact hm.trans (Nat.mod_eq_of_lt hanswer)

#print axioms low_weight_count_eq_remainders

end Quantum.Stabilizer.Homological.F2Mask.Trellis

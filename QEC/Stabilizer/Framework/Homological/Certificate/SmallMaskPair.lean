import QEC.Stabilizer.Framework.Homological.F2Mask
import Mathlib.Data.Finset.Card

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Sentinel coordinate `n` represents the empty singleton. -/
def singletonMask (n q : Nat) : Nat := if q < n then 2^q else 0

/-- An ordered pair of coordinates represents a subset of size at most two. -/
def pairMask (n q r : Nat) : Nat := singletonMask n q ^^^ singletonMask n r

/-- Set-bit support has no hidden coordinates outside a bounded mask. -/
theorem mem_mask_support {n x q : Nat} (hx : x < 2^n) :
    q ∈ (Finset.range n).filter (fun i => x.testBit i = true) ↔ x.testBit q = true := by
  rw [Finset.mem_filter,Finset.mem_range]
  constructor
  · exact And.right
  · intro hq
    refine ⟨?_,hq⟩
    by_contra hn
    have hf := Nat.testBit_lt_two_pow (lt_of_lt_of_le hx
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : n ≤ q)))
    simp [hq] at hf

/-- Every bounded mask of weight at most two has a canonical sentinel-pair encoding. -/
theorem small_mask_pair (n x : Nat) (hx : x < 2^n) (hw : bitCount n x ≤ 2) :
    ∃ q r, ((q < r ∧ r ≤ n) ∨ (q = n ∧ r = n)) ∧ x = pairMask n q r := by
  let s := (Finset.range n).filter (fun i => x.testBit i = true)
  have hs : s.card ≤ 2 := by simpa [s,bitCount_eq_card] using hw
  have hmem : ∀ q, q ∈ s ↔ x.testBit q = true := fun q => mem_mask_support hx
  have hlt : ∀ q ∈ s, q < n := fun q hq => Finset.mem_range.mp (Finset.mem_filter.mp hq).1
  by_cases hzero : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hzero
    refine ⟨n,n,Or.inr ⟨rfl,rfl⟩,?_⟩
    have hxzero : x = 0 := by
      apply Nat.zero_of_testBit_eq_false
      intro q
      have hq : x.testBit q ≠ true := by intro h; have := (hmem q).2 h; simpa [he] using this
      exact Bool.eq_false_iff.mpr hq
    simp [pairMask,singletonMask,hxzero]
  by_cases hone : s.card = 1
  · obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hone
    have hqn : q < n := hlt q (by simp [hq])
    refine ⟨q,n,Or.inl ⟨hqn,le_rfl⟩,?_⟩
    simp only [pairMask,singletonMask,hqn,if_true,lt_self_iff_false,if_false,Nat.xor_zero]
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [← hmem i,hq]
    simp only [Finset.mem_singleton,Nat.testBit_two_pow,decide_eq_true_eq]
    exact eq_comm
  have htwo : s.card = 2 := by omega
  obtain ⟨a,b,hab,hsab⟩ := Finset.card_eq_two.mp htwo
  have ha : a < n := hlt a (by simp [hsab])
  have hb : b < n := hlt b (by simp [hsab])
  have hbits : x = 2^a ^^^ 2^b := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := (hmem i).symm
    simp only [hsab,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [Nat.testBit_xor,Nat.testBit_two_pow]
    by_cases hia : i = a
    · subst i
      have hxb : x.testBit a = true := hi.mpr (Or.inl rfl)
      simp [hxb,hab,Ne.symm hab]
    · by_cases hib : i = b
      · subst i
        have hxb : x.testBit b = true := hi.mpr (Or.inr rfl)
        simp [hxb,hab,Ne.symm hab]
      · have hxf : x.testBit i = false := Bool.eq_false_iff.mpr (fun h => (hi.mp h).elim hia hib)
        simp [hxf,hia,hib,Ne.symm hia,Ne.symm hib]
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨a,b,Or.inl ⟨hab,le_of_lt hb⟩,by simpa [pairMask,singletonMask,ha,hb] using hbits⟩
  · exact ⟨b,a,Or.inl ⟨hba,le_of_lt ha⟩,by simpa [pairMask,singletonMask,ha,hb,Nat.xor_comm] using hbits⟩

#print axioms small_mask_pair
end Quantum.Stabilizer.Homological.F2Mask

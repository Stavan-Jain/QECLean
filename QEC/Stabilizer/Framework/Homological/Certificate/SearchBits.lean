import QEC.Stabilizer.Framework.Homological.Certificate.SearchTree

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Membership in a bounded bitset is exactly a true bit at an in-range index. -/
theorem mem_maskSet_iff {bits word i : Nat} :
    i ∈ maskSet bits word ↔ i < bits ∧ word.testBit i = true := by
  simp [maskSet]

/-- Clearing a known set bit erases that coordinate from its bounded support. -/
theorem maskSet_xor_two_pow {bits word q : Nat} (hq : q < bits)
    (hbit : word.testBit q = true) :
    maskSet bits (word ^^^ 2 ^ q) = (maskSet bits word).erase q := by
  ext i
  simp only [mem_maskSet_iff, Finset.mem_erase, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases he : i = q
  · subst i
    simp [hbit]
  · simp [he, Ne.symm he, and_comm]

/-- A bounded mask with empty support is zero. -/
theorem eq_zero_of_maskSet_empty {bits word : Nat} (hw : word < 2 ^ bits)
    (he : maskSet bits word = ∅) : word = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < bits
  · have hn : ¬ word.testBit i = true := by
      intro ht
      have hm := mem_maskSet_iff.mpr ⟨hi, ht⟩
      rw [he] at hm
      exact Finset.notMem_empty i hm
    simpa using Bool.eq_false_of_not_eq_true hn
  · have hp : word < 2 ^ i := hw.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_eq_false_of_lt hp]

/-- Every logarithmic parity fold is a single binary digit. -/
theorem parityFold_lt_two (k word : Nat) : parityFold k word < 2 := by
  rw [parityFold_eq]
  exact Nat.mod_lt _ (by decide)

/-- Folding XOR adds the two parities modulo two. -/
theorem parityFold_xor_add (k a b : Nat) :
    parityFold k (a ^^^ b) = (parityFold k a + parityFold k b) % 2 := by
  simp only [parityFold_eq, bitCount_xor_mod_two, Nat.add_mod, Nat.mod_mod]

/-- A residual odd parity forces a remaining coordinate in that row. -/
theorem residual_intersects_remaining (k : Nat) (row : Nat → Nat)
    (target picked word available index : Nat)
    (hsat : parityFold k (row index &&& word) = if target.testBit index then 1 else 0)
    (hres : parityResidual k row target picked index = true)
    (hsub : maskSet (2 ^ k) (word ^^^ picked) ⊆ maskSet (2 ^ k) available) :
    ∃ i ∈ maskSet (2 ^ k) (word ^^^ picked), i ∈ maskSet (2 ^ k) (row index &&& available) := by
  have hneq : parityFold k (row index &&& picked) ≠
      (if target.testBit index then 1 else 0) := by
    intro heq
    simp [parityResidual, heq] at hres
  have hp := parityFold_lt_two k (row index &&& picked)
  have ht : (if target.testBit index then 1 else 0 : Nat) < 2 := by
    split <;> decide
  have he := parityFold_xor_add k (row index &&& word) (row index &&& picked)
  rw [← Nat.and_xor_distrib_left, hsat] at he
  have hn : parityFold k (row index &&& (word ^^^ picked)) ≠ 0 := by omega
  have hc : 0 < (maskSet (2 ^ k) (row index &&& (word ^^^ picked))).card := by
    rw [maskSet_card]
    rw [parityFold_eq] at hn
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hc
  obtain ⟨hir, hit⟩ := mem_maskSet_iff.mp hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hit
  have hm := mem_maskSet_iff.mpr ⟨hir, hit.2⟩
  have ha := (mem_maskSet_iff.mp (hsub hm)).2
  exact ⟨i, hm, mem_maskSet_iff.mpr ⟨hir, by simp [Nat.testBit_and, hit.1, ha]⟩⟩

/-- A checked row separation becomes pairwise disjoint finite neighborhoods. -/
theorem paritySeparated_sound (row : Nat → Nat) (available : Nat) (rows : List Nat)
    (h : paritySeparated row available rows = true) :
    rows.Pairwise (fun r s => row r &&& row s &&& available = 0) := by
  induction rows with
  | nil => simp
  | cons r rest ih =>
    simp only [paritySeparated, Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
    exact List.pairwise_cons.mpr ⟨h.1, ih h.2⟩

/-- A zero intersection of packed rows makes their finite available neighborhoods disjoint. -/
theorem disjoint_maskSet_rows (bits r s available : Nat)
    (h : r &&& s &&& available = 0) :
    Disjoint (maskSet bits (r &&& available)) (maskSet bits (s &&& available)) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  have ha := (mem_maskSet_iff.mp hi).2
  have hb := (mem_maskSet_iff.mp hj).2
  rw [Nat.testBit_and, Bool.and_eq_true] at ha hb
  have hz := congrArg (fun x => x.testBit i) h
  simp [Nat.testBit_and, ha.1, ha.2, hb.1] at hz

#print axioms residual_intersects_remaining
end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Disjoint neighborhoods each meeting a finite support require distinct support coordinates. -/
theorem length_le_card_of_disjoint_intersections {α : Type*} [DecidableEq α]
    (sets : List (Finset α)) (target : Finset α)
    (hpair : sets.Pairwise Disjoint)
    (hmeet : ∀ s ∈ sets, ∃ i ∈ target, i ∈ s) : sets.length ≤ target.card := by
  induction sets generalizing target with
  | nil => simp
  | cons s rest ih =>
    obtain ⟨hdis, hp⟩ := List.pairwise_cons.mp hpair
    obtain ⟨i, hit, his⟩ := hmeet s List.mem_cons_self
    have hm : ∀ t ∈ rest, ∃ j ∈ target.erase i, j ∈ t := by
      intro t ht
      obtain ⟨j, hjt, hj⟩ := hmeet t (List.mem_cons_of_mem _ ht)
      refine ⟨j, Finset.mem_erase.mpr ⟨?_, hjt⟩, hj⟩
      intro he
      subst j
      exact (Finset.disjoint_left.mp (hdis t ht)) his hj
    have hc := ih (target.erase i) hp hm
    have he := Finset.card_erase_add_one hit
    simp only [List.length_cons]
    omega

end Quantum.Stabilizer.Homological.F2Mask

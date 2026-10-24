import QEC.Stabilizer.Framework.Homological.Certificate.SearchBits

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Every bounded solution admitted by a checked parity-search tree is in its candidate census. -/
theorem checkParitySearch_sound (k : Nat) (row : Nat → Nat)
    (target : Nat) (valid : Nat → Bool) (tree : ParitySearchTree) :
    ∀ available picked cap,
      checkParitySearch k row target valid tree available picked cap = true →
      ∀ word, word < 2 ^ (2 ^ k) → picked < 2 ^ (2 ^ k) →
        (∀ r, parityFold k (row r &&& word) = if target.testBit r then 1 else 0) →
        maskSet (2 ^ k) (word ^^^ picked) ⊆ maskSet (2 ^ k) available →
        (maskSet (2 ^ k) (word ^^^ picked)).card ≤ cap → valid word = true := by
  induction tree with
  | zero r =>
    intro available picked cap h word hw hp hsat hsub hcard
    simp only [checkParitySearch, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨i, _, hi⟩ := residual_intersects_remaining k row target picked word available r
      (hsat r) h.1 hsub
    rw [h.2] at hi
    simpa [maskSet] using hi
  | pack rows =>
    intro available picked cap h word hw hp hsat hsub hcard
    simp only [checkParitySearch, Bool.and_eq_true, Nat.blt_eq] at h
    have hpair : (rows.map (fun r => maskSet (2 ^ k) (row r &&& available))).Pairwise Disjoint := by
      rw [List.pairwise_map]
      exact (paritySeparated_sound row available rows h.2).imp
        (fun hrs => disjoint_maskSet_rows _ _ _ _ hrs)
    have hmeet : ∀ s ∈ rows.map (fun r => maskSet (2 ^ k) (row r &&& available)),
        ∃ i ∈ maskSet (2 ^ k) (word ^^^ picked), i ∈ s := by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
      exact residual_intersects_remaining k row target picked word available r
        (hsat r) ((List.all_eq_true.mp h.1.2) r hr) hsub
    have hc := length_le_card_of_disjoint_intersections _ _ hpair hmeet
    simp only [List.length_map] at hc
    omega
  | done =>
    intro available picked cap h word hw hp hsat hsub hcard
    simp only [checkParitySearch, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
    have he : maskSet (2 ^ k) (word ^^^ picked) = ∅ := by
      rcases h.1 with hc | ha
      · apply Finset.card_eq_zero.mp
        omega
      · subst available
        have hz : maskSet (2 ^ k) 0 = ∅ := by simp [maskSet]
        rw [hz] at hsub
        exact Finset.subset_empty.mp hsub
    have hz := eq_zero_of_maskSet_empty (Nat.xor_lt_two_pow hw hp) he
    have hword := congrArg (fun x => x ^^^ picked) hz
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at hword
    simpa only [hword] using h.2
  | split q yes no ihyes ihno =>
    intro available picked cap h word hw hp hsat hsub hcard
    simp only [checkParitySearch, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨hq, havail⟩, hyes⟩, hno⟩ := h
    by_cases hbit : (word ^^^ picked).testBit q = true
    · have hmem : q ∈ maskSet (2 ^ k) (word ^^^ picked) := mem_maskSet_iff.mpr ⟨hq, hbit⟩
      have hpos : 0 < cap := by
        have hc := Finset.card_pos.mpr ⟨q, hmem⟩
        omega
      have hc : Nat.beq cap 0 = false := by
        apply Bool.eq_false_of_not_eq_true
        intro he
        have := Nat.beq_eq.mp he
        omega
      simp only [hc, Bool.false_eq_true, if_false] at hyes
      apply ihyes (available ^^^ 2 ^ q) (picked ^^^ 2 ^ q) (cap - 1) hyes word hw
        (Nat.xor_lt_two_pow hp (Nat.pow_lt_pow_right (by decide) hq)) hsat
      · rw [← Nat.xor_assoc, maskSet_xor_two_pow hq hbit, maskSet_xor_two_pow hq havail]
        exact Finset.erase_subset_erase q hsub
      · rw [← Nat.xor_assoc, maskSet_xor_two_pow hq hbit]
        have he := Finset.card_erase_add_one hmem
        omega
    · apply ihno (available ^^^ 2 ^ q) picked cap hno word hw hp hsat ?_ hcard
      rw [maskSet_xor_two_pow hq havail]
      intro i hi
      refine Finset.mem_erase.mpr ⟨?_, hsub hi⟩
      intro he
      subst i
      exact hbit (mem_maskSet_iff.mp hi).2

/-- A zero-picked search covers all bounded words within its available support and weight budget. -/
theorem checkParitySearch_complete (k : Nat) (row : Nat → Nat)
    (target : Nat) (valid : Nat → Bool) (tree : ParitySearchTree) (available cap : Nat)
    (h : checkParitySearch k row target valid tree available 0 cap = true)
    {word : Nat} (hw : word < 2 ^ (2 ^ k))
    (hsat : ∀ r, parityFold k (row r &&& word) = if target.testBit r then 1 else 0)
    (hsub : maskSet (2 ^ k) word ⊆ maskSet (2 ^ k) available)
    (hcard : bitCount (2 ^ k) word ≤ cap) : valid word = true := by
  apply checkParitySearch_sound k row target valid tree available 0 cap h word hw
    (Nat.two_pow_pos _) hsat
  · simpa only [Nat.xor_zero] using hsub
  · simpa only [Nat.xor_zero, maskSet_card] using hcard

#print axioms checkParitySearch_complete
end Quantum.Stabilizer.Homological.F2Mask

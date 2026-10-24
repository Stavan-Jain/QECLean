import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BatchCap1Raw

noncomputable section
namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- Union the supports in an explicit list of small masks. -/
noncomputable def orList (xs : List Nat) : Nat := xs.foldr (fun a b => a ||| b) 0

/-- Every bit in a finite mask union occurs in one of its listed masks. -/
theorem orList_bit_mem (xs : List Nat) (q : Nat) (h : (orList xs).testBit q = true) :
    ∃ x ∈ xs, x.testBit q = true := by
  induction xs with
  | nil => simp [orList] at h
  | cons x xs ih =>
    simp only [orList,List.foldr_cons,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨x,by simp,h⟩
    · obtain ⟨y,hy,hq⟩ := ih h
      exact ⟨y,by simp [hy],hq⟩

/-- A nonempty coordinate of a weight-one mask uniquely determines that mask. -/
theorem singleton_eq_of_bit (bits x q : Nat) (hx : x < 2^bits)
    (hw : bitCount bits x ≤ 1) (hq : x.testBit q = true) : x = 2^q := by
  rcases small_mask_singleton bits x hx hw with hzero | ⟨p,hp,rfl⟩
  · simp [hzero] at hq
  · have he : p = q := by simpa only [Nat.testBit_two_pow,decide_eq_true_eq] using hq
    rw [he]

/-- A cap-one dual filter matching an explicit mask list proves that list complete. -/
theorem cap1_list_complete (bits k beta off : Nat) (zs allowed : List Nat)
    (hbits : bits ≤ 2^k) (hoff : off < 2^bits) (hweight : bitCount bits off ≤ 1)
    (hdisjoint : off &&& beta = 0)
    (he : ∀ z ∈ zs, parityFold k (z &&& off) = parityFold k ((z >>> bits) &&& beta))
    (hb : ∀ x ∈ allowed, x < 2^bits ∧ bitCount bits x ≤ 1)
    (ha : scalarAllowed1 bits k beta zs = orList allowed)
    (hz : scalarZero1 bits k beta zs = if allowed.contains 0 then 1 else 0) : off ∈ allowed := by
  rcases scalar_cap1_complete bits k beta off zs hbits hoff hweight hdisjoint he with
    ⟨rfl,hzero⟩ | ⟨q,hq,rfl,hbit⟩
  · rw [hz] at hzero
    have hc : allowed.contains 0 = true := by
      cases hh : allowed.contains 0 <;> simp_all
    simpa using hc
  · rw [ha] at hbit
    obtain ⟨x,hx,hbit⟩ := orList_bit_mem allowed q hbit
    rw [← singleton_eq_of_bit bits x q (hb x hx).1 (hb x hx).2 hbit]
    exact hx

#print axioms cap1_list_complete
end Quantum.Stabilizer.Homological.F2Mask

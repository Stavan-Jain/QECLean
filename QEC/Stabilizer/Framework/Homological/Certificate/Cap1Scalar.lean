import QEC.Stabilizer.Framework.Homological.Certificate.BatchCap1
import QEC.Stabilizer.Framework.Homological.Certificate.SmallMaskPair

namespace Quantum.Stabilizer.Homological.F2Mask

/-- A bounded mask of weight at most one is zero or a single coordinate. -/
theorem small_mask_singleton (n x : Nat) (hx : x < 2^n) (hw : bitCount n x ≤ 1) :
    x = 0 ∨ ∃ q < n, x = 2^q := by
  let s := (Finset.range n).filter (fun i => x.testBit i = true)
  have hs : s.card ≤ 1 := by simpa [s,bitCount_eq_card] using hw
  have hmem : ∀ q, q ∈ s ↔ x.testBit q = true := fun q => mem_mask_support hx
  by_cases hzero : s.card = 0
  · left
    have he : s = ∅ := Finset.card_eq_zero.mp hzero
    apply Nat.zero_of_testBit_eq_false
    intro q
    apply Bool.eq_false_iff.mpr
    intro h
    have := (hmem q).2 h
    simpa [he] using this
  · right
    have hone : s.card = 1 := by omega
    obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hone
    have hqn : q < n := Finset.mem_range.mp (Finset.mem_filter.mp
      (show q ∈ s by simp [hq])).1
    refine ⟨q,hqn,?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [← hmem i,hq]
    simp only [Finset.mem_singleton,Nat.testBit_two_pow,decide_eq_true_eq]
    exact eq_comm

/-- The parity of one selected coordinate reads that row bit. -/
theorem parityFold_singleton (k q row : Nat) (hq : q < 2^k) :
    parityFold k (row &&& 2^q) = if row.testBit q then 1 else 0 := by
  rw [Nat.and_two_pow]
  cases hr : row.testBit q
  · simp [hr,parityFold_eq,bitCount_eq_card]
  · simp only [hr,Bool.toNat_true,Nat.one_mul]
    rw [parityFold_eq,bitCount_eq_card]
    have he : (Finset.range (2^k)).filter (fun i => (2^q).testBit i = true) = {q} := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_range,Nat.testBit_two_pow,decide_eq_true_eq,
        Finset.mem_singleton]
      omega
    rw [he]
    simp

end Quantum.Stabilizer.Homological.F2Mask

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A row-compatible singleton is retained by the scalar bitset filter. -/
theorem scalarCompatible_bit (bits k beta z q : Nat) (hq : q < bits)
    (he : (if z.testBit q then 1 else 0) = parityFold k ((z >>> bits) &&& beta)) :
    (scalarCompatible bits k beta z).testBit q = true := by
  unfold scalarCompatible
  cases hz : z.testBit q
  · have hp : parityFold k ((z >>> bits) &&& beta) = 0 := by simpa [hz] using he.symm
    simp [hp,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_two_pow_sub_one,hq,hz]
  · have hp : parityFold k ((z >>> bits) &&& beta) = 1 := by simpa [hz] using he.symm
    simp [hp,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_two_pow_sub_one,hq,hz]

/-- A singleton satisfying every dual is retained by their intersection. -/
theorem scalarAllowed1_bit (bits k beta q : Nat) (zs : List Nat) (hq : q < bits)
    (hb : beta.testBit q = false)
    (he : ∀ z ∈ zs, (if z.testBit q then 1 else 0) = parityFold k ((z >>> bits) &&& beta)) :
    (scalarAllowed1 bits k beta zs).testBit q = true := by
  induction zs with
  | nil => simp [scalarAllowed1,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,hq,hb]
  | cons z zs ih =>
    rw [scalarAllowed1,Nat.testBit_and]
    rw [scalarCompatible_bit _ _ _ _ _ hq (he z (by simp)),ih (fun z hz => he z (by simp [hz]))]
    rfl

/-- An empty support satisfying every dual is retained by the empty-support flag. -/
theorem scalarZero1_eq_one (bits k beta : Nat) (zs : List Nat)
    (he : ∀ z ∈ zs, parityFold k ((z >>> bits) &&& beta) = 0) :
    scalarZero1 bits k beta zs = 1 := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [scalarZero1,he z (by simp),ih (fun z hz => he z (by simp [hz]))]

/-- Dual filtering is complete for outside supports of size at most one. -/
theorem scalar_cap1_complete (bits k beta off : Nat) (zs : List Nat)
    (hbits : bits ≤ 2^k) (hoff : off < 2^bits) (hweight : bitCount bits off ≤ 1)
    (hdisjoint : off &&& beta = 0)
    (he : ∀ z ∈ zs, parityFold k (z &&& off) = parityFold k ((z >>> bits) &&& beta)) :
    (off = 0 ∧ scalarZero1 bits k beta zs = 1) ∨
      ∃ q < bits, off = 2^q ∧ (scalarAllowed1 bits k beta zs).testBit q = true := by
  rcases small_mask_singleton bits off hoff hweight with hz | ⟨q,hq,rfl⟩
  · subst off
    refine Or.inl ⟨rfl,scalarZero1_eq_one bits k beta zs ?_⟩
    intro z hz
    have h := he z hz
    simpa [parityFold_eq,bitCount_eq_card] using h.symm
  · right
    refine ⟨q,hq,rfl,scalarAllowed1_bit bits k beta q zs hq ?_ ?_⟩
    · have h := congrArg (fun x : Nat => x.testBit q) hdisjoint
      simpa [Nat.testBit_and] using h
    · intro z hz
      simpa [parityFold_singleton k q z (lt_of_lt_of_le hq hbits)] using he z hz

#print axioms scalar_cap1_complete
end PackedDigits

import QEC.Stabilizer.Framework.Homological.Certificate.SearchSoundness
import QEC.Stabilizer.Framework.Homological.Certificate.MaskedAffine
import QEC.Stabilizer.Framework.Homological.Certificate.BatchLinear

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A checked parallel reconstruction gives the reconstructed mask in every individual lane. -/
theorem reconX_lane_of_batch (width size coeff output : Nat) (T : List (Nat × Nat))
    (hw : 0 < width) (hc : coeff < 2^(width*size))
    (hT : ∀ p ∈ T, p.1 < width ∧ p.2 < 2^width)
    (h : batchRecon (packF width size (fun _ => 1)) coeff T = output)
    {i : Nat} (hi : i < size) : reconX T (lane width i coeff) = lane width i output := by
  have he := batchRecon_packF width size (fun j => lane width j coeff) hw
    (fun _ _ => lane_lt _ _ _) T hT
  rw [packF_lanes width size coeff hw hc, h] at he
  have hl := congrArg (lane width i) he
  rw [lane_packF _ _ _ _ (fun j _ => reconX_lt T _ width (fun p hp => (hT p hp).2)),
    if_pos hi] at hl
  exact hl.symm

/-- All lanes beyond a bounded packed table are zero. -/
theorem lane_eq_zero_of_ge {width size value i : Nat}
    (hv : value < 2^(width*size)) (hi : size ≤ i) : lane width i value = 0 := by
  rw [lane_eq_div_mod, Nat.div_eq_of_lt (hv.trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hi)))]
  simp
end PackedDigits

namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- An empty bitset has weight zero at every finite counting width. -/
theorem bitCount_zero_mask (n : Nat) : bitCount n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitCount, ih]

/-- Removing the part of a mask inside a shadow preserves every dual annihilating that shadow. -/
theorem and_outsideMask_eq {row beta word : Nat} (h : row &&& beta = 0) :
    row &&& outsideMask word beta = row &&& word := by
  unfold outsideMask
  rw [Nat.and_xor_distrib_left]
  have hz : row &&& (word &&& beta) = 0 := by
    calc row &&& (word &&& beta) = (row &&& beta) &&& word := by ac_rfl
         _ = 0 := by rw [h, Nat.zero_and]
  rw [hz, Nat.xor_zero]

/-- A bounded shadow complement is the support outside that shadow. -/
theorem outsideMask_eq_and_complement {n word beta : Nat} (hw : word < 2^n) :
    outsideMask word beta = word &&& ((2^n-1) ^^^ beta) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [outsideMask, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < n
  · simp only [hi, decide_true, Bool.true_xor]
    cases word.testBit i <;> cases beta.testBit i <;> decide
  · have hz : word.testBit i = false := Nat.testBit_eq_false_of_lt
      (hw.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hz]

/-- Off-shadow supports fit inside the available shadow complement. -/
theorem outsideMask_support_subset {n bits word beta : Nat} (hw : word < 2^n) :
    maskSet bits (outsideMask word beta) ⊆ maskSet bits ((2^n-1) ^^^ beta) := by
  rw [outsideMask_eq_and_complement hw]
  intro i hi
  obtain ⟨hib, hit⟩ := mem_maskSet_iff.mp hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hit
  exact mem_maskSet_iff.mpr ⟨hib, hit.2⟩

/-- Increasing the counting width does not change the weight of a bounded mask. -/
theorem bitCount_eq_of_bound {n bits word : Nat} (hn : n ≤ bits) (hw : word < 2^n) :
    bitCount bits word = bitCount n word := by
  rw [show bits = n + (bits-n) by omega, bitCount_add, Nat.div_eq_of_lt hw]
  simp [bitCount_zero_mask]

/-- Verified packed duals supply every parity constraint required by a search tree. -/
theorem packed_search_constraints (k n size rows lambdas target beta rhs : Nat)
    (E T : List (Nat × Nat))
    (htranspose : ∀ lam word, lam < 2^n → word < 2^n →
      parityFold k (reconX T lam &&& word) = parityFold k (lam &&& reconX E word))
    (hT : ∀ p ∈ T, p.1 < 2^k ∧ p.2 < 2^(2^k))
    (hrows : rows < 2^((2^k)*size))
    (hlambdas : lambdas < 2^((2^k)*size)) (htarget : target < 2^size)
    (hbatch : batchRecon (packF (2^k) size (fun _ => 1)) lambdas T = rows)
    (hchecks : ∀ i < size,
      lane (2^k) i lambdas < 2^n ∧ lane (2^k) i rows &&& beta = 0 ∧
      parityFold k (lane (2^k) i lambdas &&& rhs) = if target.testBit i then 1 else 0)
    {word : Nat} (hw : word < 2^n) (he : reconX E word = rhs) :
    ∀ i, parityFold k (lane (2^k) i rows &&& outsideMask word beta) =
      if target.testBit i then 1 else 0 := by
  intro i
  by_cases hi : i < size
  · obtain ⟨hl, hon, ht⟩ := hchecks i hi
    rw [and_outsideMask_eq hon]
    have hb := reconX_lane_of_batch (2^k) size lambdas rows T (Nat.two_pow_pos _)
      hlambdas hT hbatch hi
    rw [← hb, htranspose _ _ hl hw, he, ht]
  · have hr := lane_eq_zero_of_ge hrows (Nat.le_of_not_gt hi)
    have ht : target.testBit i = false := Nat.testBit_eq_false_of_lt
      (htarget.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))
    simp [hr, ht, parityFold_eq, bitCount_zero_mask]

end Quantum.Stabilizer.Homological.F2Mask

import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial
import QEC.Stabilizer.Framework.Homological.Certificate.SmallMaskPair
namespace Quantum.Stabilizer.Homological.F2Mask

/-- Removing supported coordinates preserves the original mask bound. -/
theorem outsideMask_lt (n word beta : Nat) (hw : word < 2^n) : outsideMask word beta < 2^n := by
  exact Nat.xor_lt_two_pow hw (lt_of_le_of_lt Nat.and_le_left hw)

/-- A bounded bit mask with no set coordinates is zero. -/
theorem mask_zero_of_bitCount_zero (n x : Nat) (hx : x < 2^n) (hw : bitCount n x ≤ 0) : x = 0 := by
  have hc : ((Finset.range n).filter fun q => x.testBit q = true).card = 0 := by
    simpa [bitCount_eq_card] using Nat.eq_zero_of_le_zero hw
  have he := Finset.card_eq_zero.mp hc
  apply Nat.zero_of_testBit_eq_false
  intro q
  apply Bool.eq_false_iff.mpr
  intro hq
  have hm := (mem_mask_support hx).2 hq
  simpa [he] using hm

/-- Zero outside weight means the original word is supported on its shadow. -/
theorem supported_of_outside_weight_zero (n word beta : Nat) (hw : word < 2^n)
    (hz : bitCount n (outsideMask word beta) ≤ 0) : word &&& beta = word := by
  have he := mask_zero_of_bitCount_zero n _ (outsideMask_lt n word beta hw) hz
  have hc := congrArg (fun x => word ^^^ x) he
  simpa only [outsideMask,← Nat.xor_assoc,Nat.xor_self,Nat.zero_xor,Nat.xor_zero] using hc

end Quantum.Stabilizer.Homological.F2Mask

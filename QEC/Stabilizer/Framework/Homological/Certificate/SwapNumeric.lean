import QEC.Stabilizer.Framework.Homological.Certificate.SwapTransport

namespace PackedSwap

/-- The scalar permutation preparing a selected coefficient for deletion. -/
def source (position high state : Nat) : Nat :=
  if position < high then swap position high state else state

/-- Whole-table implementation of moving a selected state bit to the highest position. -/
def numeric (lane position high table : Nat) : Nat :=
  if position < high then
    let full := 2 ^ (lane * 2 ^ (high + 1)) - 1
    let low := 2 ^ (lane * 2 ^ high) - 1
    let zero := PackedDigits.bitZeroMask lane (high + 1) position
    let upMask := low &&& (full ^^^ zero)
    let downMask := (full ^^^ low) &&& zero
    let shift := lane * (2 ^ high - 2 ^ position)
    (table &&& (full ^^^ upMask ^^^ downMask)) |||
      ((table &&& upMask) <<< shift) ||| ((table &&& downMask) >>> shift)
  else table

/-- Preparing a state for deletion keeps it within its current bit width. -/
theorem source_lt (position high state : Nat) (hi : state < 2 ^ (high + 1)) :
    source position high state < 2 ^ (high + 1) := by
  unfold source
  split
  · exact swap_lt _ _ _ _ (by omega) (by omega) hi
  · exact hi

/-- The coefficient-preparation permutation is an involution. -/
theorem source_involutive (position high state : Nat) :
    source position high (source position high state) = state := by
  unfold source
  split
  · exact swap_involutive _ _ _ (by omega)
  · rfl

/-- Mask-based deletion is reduction of the prepared state modulo the new table size. -/
theorem forgetBit_eq_source_mod (position high state : Nat) :
    forgetBit position (high + 1) state = source position high state % 2 ^ high := by
  unfold source
  split
  · exact forgetBit_eq_swap_mod _ _ _ (by omega)
  · simp [forgetBit, show ¬position + 1 < high + 1 by omega,
      Nat.and_two_pow_sub_one_eq_mod]

/-- The efficient whole-table permutation agrees with the scalar state permutation. -/
theorem numeric_eq_packF (lane position high : Nat) (f : Nat → Nat) (hlane : 0 < lane)
    (hf : ∀ i < 2 ^ (high + 1), f i < 2 ^ lane) :
    numeric lane position high (PackedDigits.packF lane (2 ^ (high + 1)) f) =
      PackedDigits.packF lane (2 ^ (high + 1)) (fun i => f (source position high i)) := by
  unfold numeric source
  split
  next h =>
    simp only [h, ite_true]
    rw [upMask_eq_packF _ _ _ hlane h, downMask_eq_packF _ _ _ hlane h]
    exact packed_swap _ _ _ _ hlane h hf
  next h =>
    simp [h]

#print axioms source_lt
#print axioms source_involutive
#print axioms forgetBit_eq_source_mod
#print axioms numeric_eq_packF
end PackedSwap

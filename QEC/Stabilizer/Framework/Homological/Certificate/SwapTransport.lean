import QEC.Stabilizer.Framework.Homological.Certificate.PackedDigits
import QEC.Stabilizer.Framework.Homological.Certificate.SwapGeneric

namespace PackedSwap

/-- Every coordinate interchange satisfies the scalar packed-transport certificate. -/
theorem swap_checkTransport (p q i : Nat) (hpq : p < q) (hi : i < 2 ^ (q + 1)) :
    PackedDigits.checkTransport (2 ^ (q + 1)) (2 ^ q - 2 ^ p) i
      (up p q) (down p q) (swap p q) = true := by
  have hr := swap_lt p q (q + 1) i (by omega) (by omega) hi
  have hl := lowIncoming_eq_down p q i hpq hi
  have hh := highIncoming_eq_up p q i hpq hi
  have hs := swap_eq_arithmetic p q i hpq
  have huBound : up p q i = true → i + (2 ^ q - 2 ^ p) < 2 ^ (q + 1) := by
    intro hu
    rw [hs] at hr
    simpa [hu] using hr
  have hdis := up_down_disjoint p q i
  unfold PackedDigits.checkTransport
  rw [hl, hh]
  cases hu : up p q i <;> cases hd : down p q i <;>
    simp_all

/-- Swapping the high bit with a selected lower bit permutes a packed state table. -/
theorem packed_swap (width p q : Nat) (f : Nat → Nat) (hw : 0 < width) (hpq : p < q)
    (hf : ∀ i < 2 ^ (q + 1), f i < 2 ^ width) :
    (PackedDigits.packF width (2 ^ (q + 1)) f &&& ((2 ^ (width * 2 ^ (q + 1)) - 1) ^^^
      PackedDigits.packF width (2 ^ (q + 1)) (fun i => if up p q i then 2 ^ width - 1 else 0) ^^^
      PackedDigits.packF width (2 ^ (q + 1)) (fun i => if down p q i then 2 ^ width - 1 else 0))) |||
    ((PackedDigits.packF width (2 ^ (q + 1)) f &&&
      PackedDigits.packF width (2 ^ (q + 1)) (fun i => if up p q i then 2 ^ width - 1 else 0))
      <<< (width * (2 ^ q - 2 ^ p))) |||
    ((PackedDigits.packF width (2 ^ (q + 1)) f &&&
      PackedDigits.packF width (2 ^ (q + 1)) (fun i => if down p q i then 2 ^ width - 1 else 0))
      >>> (width * (2 ^ q - 2 ^ p))) =
    PackedDigits.packF width (2 ^ (q + 1)) (fun i => f (swap p q i)) := by
  exact PackedDigits.packF_swap_of_check _ _ _ _ _ _ _ hw hf
    (fun i hi => swap_checkTransport p q i hpq hi)

/-- The low-half/high-selected-bit mask is exactly the upward-moving state subset. -/
theorem upMask_eq_packF (width p q : Nat) (hw : 0 < width) (hpq : p < q) :
    (2 ^ (width * 2 ^ q) - 1) &&&
      ((2 ^ (width * 2 ^ (q + 1)) - 1) ^^^ PackedDigits.bitZeroMask width (q + 1) p) =
    PackedDigits.packF width (2 ^ (q + 1)) (fun i => if up p q i then 2 ^ width - 1 else 0) := by
  have hprefix : 2 ^ (width * 2 ^ q) - 1 =
      PackedDigits.packF width (2 ^ (q + 1))
        (fun i => if decide (i < 2 ^ q) then 2 ^ width - 1 else 0) := by
    simpa only [decide_eq_true_eq] using
      PackedDigits.prefixMask_eq_packF width (2 ^ (q + 1)) (2 ^ q) hw
        (Nat.pow_le_pow_right (by omega) (by omega))
  rw [hprefix,
    PackedDigits.lowMask_eq_packF _ _ hw, PackedDigits.bitZeroMask_eq_packF _ _ _ hw (by omega),
    PackedDigits.packF_complement_mask _ _ _ hw, PackedDigits.packF_mask_and _ _ _ _ hw]
  apply PackedDigits.packF_congr
  intro i hi
  simp [up, top_testBit q i hi, not_le, Bool.and_comm]

/-- The high-half/low-selected-bit mask is exactly the downward-moving state subset. -/
theorem downMask_eq_packF (width p q : Nat) (hw : 0 < width) (hpq : p < q) :
    ((2 ^ (width * 2 ^ (q + 1)) - 1) ^^^ (2 ^ (width * 2 ^ q) - 1)) &&&
      PackedDigits.bitZeroMask width (q + 1) p =
    PackedDigits.packF width (2 ^ (q + 1)) (fun i => if down p q i then 2 ^ width - 1 else 0) := by
  have hprefix : 2 ^ (width * 2 ^ q) - 1 =
      PackedDigits.packF width (2 ^ (q + 1))
        (fun i => if decide (i < 2 ^ q) then 2 ^ width - 1 else 0) := by
    simpa only [decide_eq_true_eq] using
      PackedDigits.prefixMask_eq_packF width (2 ^ (q + 1)) (2 ^ q) hw
        (Nat.pow_le_pow_right (by omega) (by omega))
  rw [hprefix,
    PackedDigits.lowMask_eq_packF _ _ hw, PackedDigits.bitZeroMask_eq_packF _ _ _ hw (by omega),
    PackedDigits.packF_complement_mask _ _ _ hw, PackedDigits.packF_mask_and _ _ _ _ hw]
  apply PackedDigits.packF_congr
  intro i hi
  simp [down, top_testBit q i hi, not_lt, Bool.and_comm]

#print axioms upMask_eq_packF
#print axioms downMask_eq_packF
#print axioms swap_checkTransport
#print axioms packed_swap
end PackedSwap

import QEC.Stabilizer.Framework.Homological.Certificate.PackedLaneShifts

/-!
# Packed equality flags and strict comparison

Two more sentinel-bit comparisons on packed tables of entries below
`2 ^ bits`, in lanes wider than `bits`:

* `packed_equality_flags`: the packed equality test, shifted down by `bits`,
  is the table of flags `if f i = g i then 1 else 0`;
* `packed_strict_compare_tables`: one guarded subtraction with an extra
  decrement proves `g i < f i` in every lane (`testBit_guarded_lt` is the
  scalar test).
-/

namespace PackedDigits

/-- All lane equality tests can be returned as packed zero-one flags. -/
theorem packed_equality_flags (width size bits : Nat) (f g : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size, f i < 2 ^ bits)
    (hg : ∀ i < size, g i < 2 ^ bits) :
    (packF width size (fun _ => 2 ^ bits) ^^^
      (((packF width size f ^^^ packF width size g) +
        packF width size (fun _ => 2 ^ bits - 1)) &&&
          packF width size (fun _ => 2 ^ bits))) >>> bits =
      packF width size (fun i => if f i = g i then 1 else 0) := by
  have he : packF width size (fun i => if f i = g i then 2 ^ bits else 0) =
      packF width size (fun i => (if f i = g i then 1 else 0) <<< bits) :=
    packF_congr _ _ _ _ fun i _ => by split <;> simp [Nat.shiftLeft_eq]
  rw [packed_equality_sentinels width size bits f g hb hf hg, he, ← packF_shift_left,
    Nat.shiftLeft_shiftRight]

/-- A guarded subtraction with one extra decrement detects strict inequality. -/
lemma testBit_guarded_lt (bits a b : Nat) (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    (a + 2 ^ bits - b - 1).testBit bits = decide (b < a) := by
  rw [testBit_eq_decide_le (by rw [pow_succ]; omega)]
  exact decide_eq_decide.mpr (by omega)

/-- One guarded subtraction proves all packed strict comparisons. -/
theorem packed_strict_compare_tables (width size bits : Nat) (f g : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size, f i < 2 ^ bits)
    (hg : ∀ i < size, g i < 2 ^ bits)
    (hc : ((packF width size f + packF width size (fun _ => 2 ^ bits) -
      packF width size g - packF width size (fun _ => 1)) &&&
        packF width size (fun _ => 2 ^ bits)) = packF width size (fun _ => 2 ^ bits)) :
    ∀ i < size, g i < f i := by
  have hp := two_pow_mul_two_le hb
  have hn : ∀ i < size, g i ≤ f i + 2 ^ bits := fun i hi => by have := hg i hi; omega
  have hn' : ∀ i < size, 1 ≤ f i + 2 ^ bits - g i := fun i hi => by have := hg i hi; omega
  have hfit : ∀ i < size, f i + 2 ^ bits - g i - 1 < 2 ^ width := fun i hi => by
    have := hf i hi
    omega
  rw [packF_add, packF_sub _ _ _ _ hn, packF_sub _ _ _ _ hn'] at hc
  intro i hi
  have h := testBit_of_packed_sentinel width size bits _ hb hfit hc i hi
  rwa [testBit_guarded_lt bits _ _ (hf i hi) (hg i hi), decide_eq_true_eq] at h

end PackedDigits

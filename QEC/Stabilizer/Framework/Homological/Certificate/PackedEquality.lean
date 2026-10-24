import QEC.Stabilizer.Framework.Homological.Certificate.PackedLaneShifts

namespace PackedDigits

/-- The guarded equality expression is either one sentinel or zero. -/
theorem equality_sentinel (bits a b : Nat) (ha : a < 2^bits) (hb : b < 2^bits) :
    2^bits ^^^ (((a ^^^ b)+(2^bits-1)) &&& 2^bits) =
      if a = b then 2^bits else 0 := by
  rw [Nat.and_two_pow, testBit_guarded_zero bits _ (Nat.xor_lt_two_pow ha hb)]
  by_cases h : a = b <;> simp [h, Nat.xor_eq_zero_iff]

/-- All lane equality tests can be returned as packed zero-one flags. -/
theorem packed_equality_flags (width size bits : Nat) (f g : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size, f i < 2^bits)
    (hg : ∀ i < size, g i < 2^bits) :
    (packF width size (fun _ => 2^bits) ^^^
      (((packF width size f ^^^ packF width size g) +
        packF width size (fun _ => 2^bits-1)) &&&
          packF width size (fun _ => 2^bits))) >>> bits =
      packF width size (fun i => if f i = g i then 1 else 0) := by
  have hw : 0 < width := by omega
  have hp : 2^bits < 2^width := Nat.pow_lt_pow_right (by decide) hb
  have hm : ∀ i < size, 2^bits < 2^width := fun _ _ => hp
  have hfw : ∀ i < size, f i < 2^width := fun i hi => lt_trans (hf i hi) hp
  have hgw : ∀ i < size, g i < 2^width := fun i hi => lt_trans (hg i hi) hp
  have hfit : ∀ i < size, (f i ^^^ g i)+(2^bits-1) < 2^width := by
    intro i hi
    have hx := Nat.xor_lt_two_pow (hf i hi) (hg i hi)
    have hpow : 2^(bits+1) ≤ 2^width := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hpow
    omega
  rw [packF_xor width size f g hw hfw hgw, packF_add,
    packF_and width size _ _ hw hfit hm,
    packF_xor width size _ _ hw hm (fun _ _ => lt_of_le_of_lt Nat.and_le_right hp)]
  have he : packF width size (fun i => 2^bits ^^^
      (((f i ^^^ g i)+(2^bits-1)) &&& 2^bits)) =
      packF width size (fun i => (if f i = g i then 1 else 0) <<< bits) := by
    apply packF_congr
    intro i hi
    rw [equality_sentinel bits _ _ (hf i hi) (hg i hi)]
    split <;> simp [Nat.shiftLeft_eq]
  rw [he]
  rw [← packF_shift_left width size bits (fun i => if f i = g i then 1 else 0)]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- A guarded subtraction with one extra decrement detects strict inequality. -/
theorem testBit_guarded_lt (bits a b : Nat) (ha : a < 2^bits) (hb : b < 2^bits) :
    (a+2^bits-b-1).testBit bits = decide (b<a) := by
  have hp := Nat.two_pow_pos bits
  have hr : a+2^bits-b-1 < 2^(bits+1) := by rw [pow_succ]; omega
  have h := not_testBit_eq_decide_mod_lt (a+2^bits-b-1) bits
  rw [Nat.mod_eq_of_lt hr] at h
  have he : a+2^bits-b-1 < 2^bits ↔ ¬b<a := by omega
  simp only [he, decide_not] at h
  simpa using congrArg Bool.not h

/-- One guarded subtraction proves all packed strict comparisons. -/
theorem packed_strict_compare_tables (width size bits : Nat) (f g : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size, f i < 2^bits)
    (hg : ∀ i < size, g i < 2^bits)
    (hc : ((packF width size f + packF width size (fun _ => 2^bits) -
      packF width size g - packF width size (fun _ => 1)) &&&
        packF width size (fun _ => 2^bits)) = packF width size (fun _ => 2^bits)) :
    ∀ i < size, g i < f i := by
  have hn : ∀ i < size, g i ≤ f i+2^bits := fun i hi => by have := hg i hi; omega
  have hn' : ∀ i < size, 1 ≤ f i+2^bits-g i := fun i hi => by have := hg i hi; omega
  have hm : ∀ i < size, 2^bits < 2^width := fun _ _ => Nat.pow_lt_pow_right (by decide) hb
  have hfit : ∀ i < size, f i+2^bits-g i-1 < 2^width := by
    intro i hi
    have hfi := hf i hi
    have hp : 2^(bits+1) ≤ 2^width := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hp
    omega
  rw [packF_add, packF_sub _ _ _ _ hn, packF_sub _ _ _ _ hn'] at hc
  intro i hi
  have h := congrArg (fun v => (lane width i v).testBit bits) hc
  dsimp only at h
  rw [lane_and, Nat.testBit_and, lane_packF _ _ _ _ hfit, lane_packF _ _ _ _ hm] at h
  simp only [if_pos hi, Nat.testBit_two_pow_self, Bool.and_true] at h
  rw [testBit_guarded_lt bits _ _ (hf i hi) (hg i hi)] at h
  exact of_decide_eq_true h

/-- Packing commutes with a finite sum of lane tables. -/
theorem packF_list_sum (width size : Nat) (tables : List (Nat → Nat)) :
    (tables.map (packF width size)).sum =
      packF width size (fun i => (tables.map (fun f => f i)).sum) := by
  induction tables with
  | nil => simp [packF]
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons, ih, packF_add]

end PackedDigits

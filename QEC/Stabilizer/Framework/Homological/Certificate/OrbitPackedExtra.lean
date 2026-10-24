import QEC.Stabilizer.Framework.Homological.Certificate.PackedDigits

namespace PackedDigits

/-- Subtracting a pointwise smaller packed table subtracts in every lane. -/
theorem packF_sub (width size : Nat) (f g : Nat → Nat)
    (h : ∀ i < size, g i ≤ f i) :
    packF width size f - packF width size g = packF width size (fun i => f i - g i) := by
  have heq : packF width size (fun i => f i - g i) + packF width size g =
      packF width size f := by
    rw [packF_add]
    apply packF_congr
    intro i hi
    exact Nat.sub_add_cancel (h i hi)
  omega

/-- Multiplication by a scalar multiplies every algebraically packed lane. -/
theorem packF_mul (width size scalar : Nat) (f : Nat → Nat) :
    scalar * packF width size f = packF width size (fun i => scalar * f i) := by
  simp only [packF, Nat.mul_ofDigits, List.map_map, Function.comp_def]

/-- A sentinel bit in a guarded subtraction compares two bounded values. -/
theorem testBit_guarded_sub (bits a b : Nat) (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    (a + 2 ^ bits - b).testBit bits = decide (b ≤ a) := by
  have hpos := Nat.two_pow_pos bits
  have hrange : a + 2 ^ bits - b < 2 ^ (bits + 1) := by
    rw [pow_succ]
    omega
  have hmod : (a + 2 ^ bits - b) % 2 ^ (bits + 1) = a + 2 ^ bits - b :=
    Nat.mod_eq_of_lt hrange
  have h := not_testBit_eq_decide_mod_lt (a + 2 ^ bits - b) bits
  rw [hmod] at h
  have hlt : a + 2 ^ bits - b < 2 ^ bits ↔ ¬ b ≤ a := by omega
  simp only [hlt, decide_not] at h
  simpa using congrArg Bool.not h

/-- The sentinel comparison in a packed table is a separate comparison in every lane. -/
theorem lane_guarded_sub (width size bits scalar i : Nat) (f : Nat → Nat)
    (hbits : bits < width) (hf : ∀ j < size, f j < 2 ^ bits)
    (hs : scalar < 2 ^ bits) (hi : i < size) :
    (lane width i ((packF width size f + packF width size (fun _ => 2 ^ bits)) -
      packF width size (fun _ => scalar))).testBit bits = decide (scalar ≤ f i) := by
  rw [packF_add, packF_sub _ _ _ _ (fun j hj => by have := hf j hj; omega)]
  have hfit : ∀ j < size, f j + 2 ^ bits - scalar < 2 ^ width := by
    intro j hj
    have hp : 2 ^ (bits + 1) ≤ 2 ^ width := Nat.pow_le_pow_right (by omega) (by omega)
    have hj' := hf j hj
    rw [pow_succ] at hp
    omega
  rw [lane_packF _ _ _ _ hfit, if_pos hi]
  exact testBit_guarded_sub bits (f i) scalar (hf i hi) hs

/-- A successful simultaneous guarded comparison proves each lane comparison. -/
theorem packed_guarded_sub_sound (width size bits scalar : Nat) (f : Nat → Nat)
    (hbits : bits < width) (hf : ∀ j < size, f j < 2 ^ bits)
    (hs : scalar < 2 ^ bits)
    (hcheck : ((packF width size f + packF width size (fun _ => 2 ^ bits)) -
      packF width size (fun _ => scalar)) &&& packF width size (fun _ => 2 ^ bits) =
      packF width size (fun _ => 2 ^ bits)) :
    ∀ i < size, scalar ≤ f i := by
  intro i hi
  have hm : ∀ j < size, 2 ^ bits < 2 ^ width := by
    intro j hj
    exact Nat.pow_lt_pow_right (by decide) hbits
  have h := congrArg (fun value => (lane width i value).testBit bits) hcheck
  dsimp only at h
  rw [lane_and, Nat.testBit_and, lane_packF _ _ _ _ hm, if_pos hi,
    Nat.testBit_two_pow_self, Bool.and_true] at h
  rw [lane_guarded_sub width size bits scalar i f hbits hf hs hi] at h
  exact of_decide_eq_true h

end PackedDigits

namespace PackedDigits

/-- A zero-test uses the carry into the sentinel bit after adding one less than its value. -/
theorem testBit_guarded_zero (bits value : Nat) (hv : value < 2 ^ bits) :
    (value + (2 ^ bits - 1)).testBit bits = decide (value ≠ 0) := by
  have hp := Nat.two_pow_pos bits
  have hr : value + (2 ^ bits - 1) < 2 ^ (bits + 1) := by rw [pow_succ]; omega
  have h := not_testBit_eq_decide_mod_lt (value + (2 ^ bits - 1)) bits
  rw [Nat.mod_eq_of_lt hr] at h
  have he : value + (2 ^ bits - 1) < 2 ^ bits ↔ ¬ value ≠ 0 := by omega
  simp only [he, decide_not] at h
  simpa using congrArg Bool.not h

/-- A bit within a packed table lane is the same bit of the table entry. -/
theorem testBit_packF_at (width size index bit : Nat) (f : Nat → Nat)
    (hf : ∀ j < size, f j < 2 ^ width) (hb : bit < width) :
    (packF width size f).testBit (width * index + bit) =
      if index < size then (f index).testBit bit else false := by
  have h := testBit_lane width index (packF width size f) bit
  rw [lane_packF _ _ _ _ hf] at h
  by_cases hi : index < size <;> simpa [hb, hi] using h.symm

/-- The comparison mask for equality is exact in each packed lane. -/
theorem packed_equal_mask_bit (width size bits scalar i : Nat) (f : Nat → Nat)
    (hbits : bits < width) (hf : ∀ j < size, f j < 2 ^ bits)
    (hs : scalar < 2 ^ bits) (hi : i < size) :
    (lane width i (packF width size (fun _ => 2 ^ bits) ^^^
      (((packF width size f ^^^ packF width size (fun _ => scalar)) +
        packF width size (fun _ => 2 ^ bits - 1)) &&&
        packF width size (fun _ => 2 ^ bits)))).testBit bits = decide (f i = scalar) := by
  have hw : 0 < width := by omega
  have hm : ∀ j < size, 2 ^ bits < 2 ^ width := fun _ _ =>
    Nat.pow_lt_pow_right (by decide) hbits
  have hfw : ∀ j < size, f j < 2 ^ width := fun j hj => lt_trans (hf j hj) (hm j hj)
  have hsw : ∀ j < size, scalar < 2 ^ width := fun j hj => lt_trans hs (hm j hj)
  have hxor : ∀ j < size, f j ^^^ scalar < 2 ^ bits := fun j hj =>
    Nat.xor_lt_two_pow (hf j hj) hs
  have hfit : ∀ j < size, (f j ^^^ scalar) + (2 ^ bits - 1) < 2 ^ width := by
    intro j hj
    have hp := Nat.pow_le_pow_right (n := 2) (by omega) (show bits + 1 ≤ width by omega)
    have hj' := hxor j hj
    rw [pow_succ] at hp
    omega
  rw [packF_xor _ _ _ _ hw hfw hsw, packF_add, lane_xor, lane_and,
    lane_packF _ _ _ _ hm, lane_packF _ _ _ _ hfit, if_pos hi,
    Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true]
  simp only [if_pos hi]
  rw [testBit_guarded_zero bits _ (hxor i hi)]
  simp only [Bool.true_xor, ← decide_not, not_not, Nat.xor_eq_zero_iff]

end PackedDigits

namespace PackedDigits

/-- Concatenating two finite tables concatenates their packed lane blocks. -/
theorem packF_append (width left right : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < left, f i < 2 ^ width) (hg : ∀ i < right, g i < 2 ^ width) :
    packF width left f ||| (packF width right g <<< (width * left)) =
      packF width (left + right) (fun i => if i < left then f i else g (i - left)) := by
  have hh : ∀ i < left + right, (if i < left then f i else g (i - left)) < 2 ^ width := by
    intro i hi
    split
    · exact hf i (by assumption)
    · exact hg (i - left) (by omega)
  apply eq_of_lane_eq hw
  intro i
  rw [lane_or, lane_packF _ _ _ _ hf, lane_shiftLeft _ _ _ _ hw,
    lane_packF _ _ _ _ hg, lane_packF _ _ _ _ hh]
  by_cases hi : i < left
  · simp [hi, show ¬ left ≤ i by omega, show i < left + right by omega]
  · have hi' : left ≤ i := by omega
    by_cases hir : i < left + right
    · simp [hi, hi', hir, show i - left < right by omega]
    · simp [hi, hi', hir, show ¬ i - left < right by omega]

end PackedDigits

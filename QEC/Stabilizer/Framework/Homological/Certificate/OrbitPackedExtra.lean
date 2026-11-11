import QEC.Stabilizer.Framework.Homological.Certificate.PackedDigits

/-!
# Sentinel-bit comparisons on packed tables

When the entries of a packed table are below `2 ^ bits` and the lanes are wider
than `bits`, bit `bits` of every lane is free. An addition or subtraction
arranged so that this *sentinel* bit of the result records a comparison then
compares every entry of the table in one packed operation.

* Scalar sentinel tests: `testBit_guarded_sub` (`b ≤ a`),
  `testBit_guarded_zero` (`value ≠ 0`) and `equality_sentinel` (`a = b`).
* `testBit_of_packed_sentinel`: if masking a packed table with the packed
  sentinel bits returns all of them, every entry has its sentinel bit set.
* `packed_compare_tables` and `packed_guarded_sub_sound`: one guarded
  subtraction proves `g i ≤ f i`, respectively `scalar ≤ f i`, in every lane;
  `lane_guarded_sub` reads the sentinel of a single lane.
* `packed_equality_sentinels` and `packed_equal_mask_bit`: the packed equality
  test leaves the sentinel bit exactly in the lanes where two tables agree.
* `packed_mask_bound`: a packed low-bit mask proves a bound on every entry.
-/

namespace PackedDigits

/-! ## Scalar sentinel tests -/

/-- A sentinel bit in a guarded subtraction compares two bounded values. -/
lemma testBit_guarded_sub (bits a b : Nat) (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    (a + 2 ^ bits - b).testBit bits = decide (b ≤ a) := by
  rw [testBit_eq_decide_le (by rw [pow_succ]; omega)]
  exact decide_eq_decide.mpr (by omega)

/-- A zero-test uses the carry into the sentinel bit after adding one
less than its value. -/
lemma testBit_guarded_zero (bits value : Nat) (hv : value < 2 ^ bits) :
    (value + (2 ^ bits - 1)).testBit bits = decide (value ≠ 0) := by
  have := Nat.two_pow_pos bits
  rw [testBit_eq_decide_le (by rw [pow_succ]; omega)]
  exact decide_eq_decide.mpr (by omega)

/-- The guarded equality expression is either one sentinel or zero. -/
lemma equality_sentinel (bits a b : Nat) (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    2 ^ bits ^^^ (((a ^^^ b) + (2 ^ bits - 1)) &&& 2 ^ bits) =
      if a = b then 2 ^ bits else 0 := by
  rw [Nat.and_two_pow, testBit_guarded_zero bits _ (Nat.xor_lt_two_pow ha hb)]
  by_cases h : a = b <;> simp [h, Nat.xor_eq_zero_iff]

/-! ## Comparing every lane at once -/

/-- If masking a packed table with the packed sentinel bits returns all of
them, every entry of the table has its sentinel bit set. -/
theorem testBit_of_packed_sentinel (width size bits : Nat) (h : Nat → Nat)
    (hb : bits < width) (hfit : ∀ i < size, h i < 2 ^ width)
    (hc : packF width size h &&& packF width size (fun _ => 2 ^ bits) =
      packF width size (fun _ => 2 ^ bits)) :
    ∀ i < size, (h i).testBit bits = true := by
  intro i hi
  have hm : ∀ j < size, 2 ^ bits < 2 ^ width := fun _ _ =>
    Nat.pow_lt_pow_right (by decide) hb
  have hl := congrArg (fun v => (lane width i v).testBit bits) hc
  simpa [lane_and, lane_packF _ _ _ _ hfit, lane_packF _ _ _ _ hm, hi] using hl

/-- Guarded subtraction compares two bounded tables simultaneously. -/
theorem packed_compare_tables (width size bits : Nat) (f g : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size, f i < 2 ^ bits)
    (hg : ∀ i < size, g i < 2 ^ bits)
    (hc : ((packF width size f + packF width size (fun _ => 2 ^ bits) -
      packF width size g) &&& packF width size (fun _ => 2 ^ bits)) =
      packF width size (fun _ => 2 ^ bits)) : ∀ i < size, g i ≤ f i := by
  have hp := two_pow_mul_two_le hb
  have hn : ∀ i < size, g i ≤ f i + 2 ^ bits := fun i hi => by have := hg i hi; omega
  have hfit : ∀ i < size, f i + 2 ^ bits - g i < 2 ^ width := fun i hi => by
    have := hf i hi
    omega
  rw [packF_add, packF_sub _ _ _ _ hn] at hc
  intro i hi
  have h := testBit_of_packed_sentinel width size bits _ hb hfit hc i hi
  rwa [testBit_guarded_sub bits _ _ (hf i hi) (hg i hi), decide_eq_true_eq] at h

/-- A successful simultaneous guarded comparison proves each lane comparison. -/
theorem packed_guarded_sub_sound (width size bits scalar : Nat) (f : Nat → Nat)
    (hbits : bits < width) (hf : ∀ j < size, f j < 2 ^ bits)
    (hs : scalar < 2 ^ bits)
    (hcheck : ((packF width size f + packF width size (fun _ => 2 ^ bits)) -
      packF width size (fun _ => scalar)) &&& packF width size (fun _ => 2 ^ bits) =
      packF width size (fun _ => 2 ^ bits)) :
    ∀ i < size, scalar ≤ f i :=
  packed_compare_tables width size bits f (fun _ => scalar) hbits hf (fun _ _ => hs) hcheck

/-- The sentinel comparison in a packed table is a separate comparison in
every lane. -/
lemma lane_guarded_sub (width size bits scalar i : Nat) (f : Nat → Nat)
    (hbits : bits < width) (hf : ∀ j < size, f j < 2 ^ bits)
    (hs : scalar < 2 ^ bits) (hi : i < size) :
    (lane width i ((packF width size f + packF width size (fun _ => 2 ^ bits)) -
      packF width size (fun _ => scalar))).testBit bits = decide (scalar ≤ f i) := by
  have hp := two_pow_mul_two_le hbits
  have hn : ∀ j < size, scalar ≤ f j + 2 ^ bits := fun j _ => by omega
  have hfit : ∀ j < size, f j + 2 ^ bits - scalar < 2 ^ width := fun j hj => by
    have := hf j hj
    omega
  rw [packF_add, packF_sub _ _ _ _ hn, lane_packF _ _ _ _ hfit, if_pos hi]
  exact testBit_guarded_sub bits (f i) scalar (hf i hi) hs

/-- The packed equality test leaves the sentinel bit exactly in the lanes
where the two tables agree. -/
theorem packed_equality_sentinels (width size bits : Nat) (f g : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size, f i < 2 ^ bits)
    (hg : ∀ i < size, g i < 2 ^ bits) :
    packF width size (fun _ => 2 ^ bits) ^^^
      (((packF width size f ^^^ packF width size g) +
        packF width size (fun _ => 2 ^ bits - 1)) &&&
          packF width size (fun _ => 2 ^ bits)) =
      packF width size (fun i => if f i = g i then 2 ^ bits else 0) := by
  have hw : 0 < width := by omega
  have hp : 2 ^ bits < 2 ^ width := Nat.pow_lt_pow_right (by decide) hb
  have hp2 := two_pow_mul_two_le hb
  have hfit : ∀ i < size, (f i ^^^ g i) + (2 ^ bits - 1) < 2 ^ width := fun i hi => by
    have := Nat.xor_lt_two_pow (hf i hi) (hg i hi)
    omega
  rw [packF_xor width size f g hw (fun i hi => (hf i hi).trans hp)
      (fun i hi => (hg i hi).trans hp), packF_add,
    packF_and width size _ _ hw hfit (fun _ _ => hp),
    packF_xor width size _ _ hw (fun _ _ => hp)
      (fun _ _ => lt_of_le_of_lt Nat.and_le_right hp)]
  exact packF_congr _ _ _ _ fun i hi => equality_sentinel bits _ _ (hf i hi) (hg i hi)

/-- The comparison mask for equality is exact in each packed lane. -/
lemma packed_equal_mask_bit (width size bits scalar i : Nat) (f : Nat → Nat)
    (hbits : bits < width) (hf : ∀ j < size, f j < 2 ^ bits)
    (hs : scalar < 2 ^ bits) (hi : i < size) :
    (lane width i (packF width size (fun _ => 2 ^ bits) ^^^
      (((packF width size f ^^^ packF width size (fun _ => scalar)) +
        packF width size (fun _ => 2 ^ bits - 1)) &&&
        packF width size (fun _ => 2 ^ bits)))).testBit bits = decide (f i = scalar) := by
  have hp : 2 ^ bits < 2 ^ width := Nat.pow_lt_pow_right (by decide) hbits
  have hfit : ∀ j < size, (if f j = scalar then 2 ^ bits else 0) < 2 ^ width := fun j _ => by
    split
    · exact hp
    · exact Nat.two_pow_pos _
  rw [packed_equality_sentinels width size bits f (fun _ => scalar) hbits hf (fun _ _ => hs),
    lane_packF _ _ _ _ hfit, if_pos hi]
  by_cases h : f i = scalar <;> simp [h]

/-- A packed low-bit mask certifies a smaller bound on every table entry. -/
theorem packed_mask_bound (width size bits : Nat) (f : Nat → Nat)
    (hb : bits ≤ width) (hf : ∀ i < size, f i < 2 ^ width)
    (hc : packF width size f &&& packF width size (fun _ => 2 ^ bits - 1) =
      packF width size f) : ∀ i < size, f i < 2 ^ bits := by
  have hm : ∀ i < size, 2 ^ bits - 1 < 2 ^ width := fun _ _ =>
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      (Nat.pow_le_pow_right Nat.two_pos hb)
  intro i hi
  have h := congrArg (lane width i) hc
  rw [lane_and, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hm, if_pos hi, if_pos hi,
    Nat.and_two_pow_sub_one_eq_mod] at h
  rw [← h]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

end PackedDigits

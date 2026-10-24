import QEC.Stabilizer.Framework.Homological.Certificate.PackedEquality
namespace PackedDigits

/-- Dropping an initial lane shifts every remaining lane index by one. -/
theorem packF_drop_one (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size+1, f i < 2^width) :
    packF width (size+1) f >>> width = packF width size (fun i => f (i+1)) := by
  apply eq_of_lane_eq hw
  intro i
  rw [show lane width i (packF width (size+1) f >>> width) =
      lane width (i+1) (packF width (size+1) f) by
    simpa only [Nat.mul_one] using lane_shiftRight width i 1 (packF width (size+1) f)]
  rw [lane_packF _ _ _ _ hf, lane_packF _ _ _ _ (fun j hj => hf (j+1) (by omega))]
  split_ifs <;> omega

/-- A shorter payload mask retains exactly the indicated prefix of bounded lanes. -/
theorem packF_mask_prefix (width size count bits : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hb : bits ≤ width) (hc : count ≤ size)
    (hf : ∀ i < size, f i < 2^bits) :
    packF width size f &&& packF width count (fun _ => 2^bits-1) = packF width count f := by
  have hfw : ∀ i < size, f i < 2^width := fun i hi =>
    lt_of_lt_of_le (hf i hi) (Nat.pow_le_pow_right (by decide) hb)
  have hmask : ∀ i < count, 2^bits-1 < 2^width := by
    intro i hi
    have := Nat.two_pow_pos bits
    have := Nat.pow_le_pow_right (n := 2) (by decide) hb
    omega
  apply eq_of_lane_eq hw
  intro i
  rw [lane_and, lane_packF _ _ _ _ hfw, lane_packF _ _ _ _ hmask,
    lane_packF _ _ _ _ (fun i hi => hfw i (by omega))]
  by_cases hi : i < count
  · simp [hi, show i < size by omega, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (hf i (by omega))]
  · simp [hi]

/-- The adjacent-lane guarded subtraction certifies a strictly increasing table. -/
theorem packed_adjacent_strict (width size bits : Nat) (f : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size+1, f i < 2^bits)
    (hc : (((packF width (size+1) f >>> width) +
      (packF width size (fun _ => 1) <<< bits) -
      (packF width (size+1) f &&& (packF width size (fun _ => 1)*(2^bits-1))) -
      packF width size (fun _ => 1)) &&&
        (packF width size (fun _ => 1) <<< bits)) =
          (packF width size (fun _ => 1) <<< bits)) :
    ∀ i < size, f i < f (i+1) := by
  have hfw : ∀ i < size+1, f i < 2^width := fun i hi =>
    lt_trans (hf i hi) (Nat.pow_lt_pow_right (by decide) hb)
  rw [packF_drop_one width size f (by omega) hfw, repeat_mul_eq_packF,
    packF_mask_prefix width (size+1) size bits f (by omega) (by omega) (by omega) hf,
    packF_shift_left] at hc
  simp only [Nat.shiftLeft_eq, Nat.one_mul] at hc
  exact packed_strict_compare_tables width size bits (fun i => f (i+1)) f hb
    (fun i hi => hf (i+1) (by omega)) (fun i hi => hf i (by omega)) hc

end PackedDigits

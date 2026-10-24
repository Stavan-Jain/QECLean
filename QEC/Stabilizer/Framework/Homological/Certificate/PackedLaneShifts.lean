import QEC.Stabilizer.Framework.Homological.Certificate.OrbitPackedExtra
namespace PackedDigits

/-- Operator notation for the entrywise packed left-shift identity. -/
theorem packF_shift_left (width size shift : Nat) (f : Nat → Nat) :
    (packF width size f) <<< shift =
      packF width size (fun i => (f i) <<< shift) :=
  packF_shiftLeft width size shift f

/-- A masked right shift acts independently inside every packed lane. -/
theorem masked_shiftRight_packF (width size shift mask : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width) (hm : mask < 2 ^ width)
    (hs : ∀ j < width, width ≤ j + shift → mask.testBit j = false) :
    (packF width size f >>> shift) &&& packF width size (fun _ => mask) =
      packF width size (fun i => (f i >>> shift) &&& mask) := by
  have hout : ∀ i < size, (f i >>> shift) &&& mask < 2 ^ width :=
    fun i hi => lt_of_le_of_lt Nat.and_le_right hm
  apply Nat.eq_of_testBit_eq
  intro k
  obtain ⟨i,j,hj,rfl⟩ : ∃ i j, j < width ∧ k = width*i+j :=
    ⟨k/width,k%width,Nat.mod_lt _ hw, by have h := Nat.mod_add_div k width; omega⟩
  rw [Nat.testBit_and, Nat.testBit_shiftRight,
    testBit_packF_at width size i j _ (fun _ _ => hm) hj,
    testBit_packF_at width size i j _ hout hj]
  by_cases hi : i < size
  · simp only [hi, if_true, Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases hb : j + shift < width
    · have he : shift+(width*i+j) = width*i+(j+shift) := by omega
      rw [he, testBit_packF_at width size i (j+shift) f hf hb, if_pos hi]
      rw [Nat.add_comm j shift]
    · rw [hs j hj (by omega)]
      simp
  · simp [hi]

/-- A masked left shift acts independently when the mask excludes incoming low bits. -/
theorem masked_shiftLeft_packF (width size shift mask : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width) (hm : mask < 2 ^ width)
    (hs : ∀ j < width, j < shift → mask.testBit j = false) :
    (packF width size f <<< shift) &&& packF width size (fun _ => mask) =
      packF width size (fun i => (f i <<< shift) &&& mask) := by
  have hout : ∀ i < size, (f i <<< shift) &&& mask < 2 ^ width :=
    fun i hi => lt_of_le_of_lt Nat.and_le_right hm
  apply Nat.eq_of_testBit_eq
  intro k
  obtain ⟨i,j,hj,rfl⟩ : ∃ i j, j < width ∧ k = width*i+j :=
    ⟨k/width,k%width,Nat.mod_lt _ hw, by have h := Nat.mod_add_div k width; omega⟩
  rw [Nat.testBit_and, Nat.testBit_shiftLeft,
    testBit_packF_at width size i j _ (fun _ _ => hm) hj,
    testBit_packF_at width size i j _ hout hj]
  by_cases hi : i < size
  · simp only [hi, if_true, Nat.testBit_and, Nat.testBit_shiftLeft]
    by_cases hb : shift ≤ j
    · have he : width*i+j-shift = width*i+(j-shift) := by omega
      rw [he, testBit_packF_at width size i (j-shift) f hf (by omega), if_pos hi]
      simp [hb, show shift ≤ width*i+j by omega]
    · rw [hs j hj (by omega)]
      simp
  · simp [hi]

/-- A packed repetition word produces a constant lane table by multiplication. -/
theorem repeat_mul_eq_packF (width size value : Nat) :
    packF width size (fun _ => 1) * value = packF width size (fun _ => value) := by
  rw [Nat.mul_comm, packF_mul]
  simp only [Nat.mul_one]

/-- Guarded subtraction compares two bounded tables simultaneously. -/
theorem packed_compare_tables (width size bits : Nat) (f g : Nat → Nat)
    (hb : bits < width) (hf : ∀ i < size, f i < 2 ^ bits)
    (hg : ∀ i < size, g i < 2 ^ bits)
    (hc : ((packF width size f + packF width size (fun _ => 2 ^ bits) -
      packF width size g) &&& packF width size (fun _ => 2 ^ bits)) =
      packF width size (fun _ => 2 ^ bits)) : ∀ i < size, g i ≤ f i := by
  have hm : ∀ i < size, 2 ^ bits < 2 ^ width := fun _ _ =>
    Nat.pow_lt_pow_right (by decide) hb
  have hn : ∀ i < size, g i ≤ f i + 2 ^ bits := fun i hi => by have := hg i hi; omega
  have hfit : ∀ i < size, f i + 2 ^ bits - g i < 2 ^ width := by
    intro i hi
    have hfi := hf i hi
    have hp : 2^(bits+1) ≤ 2^width := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hp
    omega
  rw [packF_add, packF_sub _ _ _ _ hn] at hc
  intro i hi
  have h := congrArg (fun v => (lane width i v).testBit bits) hc
  dsimp only at h
  rw [lane_and, Nat.testBit_and, lane_packF _ _ _ _ hfit,
    lane_packF _ _ _ _ hm] at h
  simp only [if_pos hi, Nat.testBit_two_pow_self, Bool.and_true] at h
  rw [testBit_guarded_sub bits _ _ (hf i hi) (hg i hi)] at h
  exact of_decide_eq_true h

/-- A packed low-bit mask certifies a smaller bound on every table entry. -/
theorem packed_mask_bound (width size bits : Nat) (f : Nat → Nat)
    (hb : bits ≤ width) (hf : ∀ i < size, f i < 2^width)
    (hc : packF width size f &&& packF width size (fun _ => 2^bits-1) =
      packF width size f) : ∀ i < size, f i < 2^bits := by
  have hm : ∀ i < size, 2^bits-1 < 2^width := by
    intro i hi
    have hp := Nat.two_pow_pos bits
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hb
    omega
  intro i hi
  have h := congrArg (lane width i) hc
  rw [lane_and, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hm] at h
  simp only [if_pos hi] at h
  have hle : f i ≤ 2^bits-1 := by
    rw [← h]
    exact Nat.and_le_right
  have hp := Nat.two_pow_pos bits
  omega

end PackedDigits

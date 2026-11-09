import QEC.Stabilizer.Framework.Homological.Certificate.OrbitPackedExtra

/-!
# Shifts inside the lanes of a packed table

Shifting a packed table by fewer bits than the lane width moves bits across
lane boundaries. A mask applied after the shift removes exactly the bits that
crossed, so the masked shift acts as the entrywise shift:

* `packF_shiftRight_and_of_testBit`: a right shift followed by a packed mask
  table whose entries vanish on the top `shift` bits of each lane;
  `masked_shiftRight_packF` (constant mask) and `packF_shiftRight_and` (mask
  entries below `2 ^ bits` with `bits + shift ≤ width`) are its special cases.
* `masked_shiftLeft_packF`: a left shift followed by a constant mask that
  vanishes on the low `shift` bits of each lane.
* `packF_selectBit`: one chosen bit of every entry, as a table of zeros and
  ones.
-/

namespace PackedDigits

/-- A right shift followed by a mask table acts independently inside every
packed lane, provided no mask entry has a bit among the top `shift` bits of
its lane. -/
theorem packF_shiftRight_and_of_testBit (width size shift : Nat) (f g : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ width)
    (hs : ∀ i < size, ∀ j < width, width ≤ j + shift → (g i).testBit j = false) :
    (packF width size f >>> shift) &&& packF width size g =
      packF width size (fun i => (f i >>> shift) &&& g i) := by
  have hout : ∀ i < size, (f i >>> shift) &&& g i < 2 ^ width :=
    fun i hi => lt_of_le_of_lt Nat.and_le_right (hg i hi)
  refine Nat.eq_of_testBit_eq fun k => ?_
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < width ∧ k = width * i + j :=
    ⟨k / width, k % width, Nat.mod_lt _ hw, (Nat.div_add_mod k width).symm⟩
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_packF_at width size i j _ hg hj,
    testBit_packF_at width size i j _ hout hj]
  by_cases hi : i < size
  · simp only [hi, if_true, Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases hb : j + shift < width
    · rw [show shift + (width * i + j) = width * i + (j + shift) by omega,
        testBit_packF_at width size i (j + shift) f hf hb, if_pos hi, Nat.add_comm j shift]
    · rw [hs i hi j hj (by omega)]
      simp
  · simp [hi]

/-- A masked right shift acts independently inside every packed lane. -/
lemma masked_shiftRight_packF (width size shift mask : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width) (hm : mask < 2 ^ width)
    (hs : ∀ j < width, width ≤ j + shift → mask.testBit j = false) :
    (packF width size f >>> shift) &&& packF width size (fun _ => mask) =
      packF width size (fun i => (f i >>> shift) &&& mask) :=
  packF_shiftRight_and_of_testBit width size shift f (fun _ => mask) hw hf (fun _ _ => hm)
    (fun _ _ => hs)

/-- A right shift followed by a sufficiently short mask cannot mix
adjacent lanes. -/
lemma packF_shiftRight_and (width size bits shift : Nat) (f g : Nat → Nat)
    (hw : 0 < width) (hfit : bits + shift ≤ width)
    (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ bits) :
    (packF width size f >>> shift) &&& packF width size g =
      packF width size (fun i => (f i >>> shift) &&& g i) :=
  packF_shiftRight_and_of_testBit width size shift f g hw hf
    (fun i hi => (hg i hi).trans_le (Nat.pow_le_pow_right Nat.two_pos (by omega)))
    (fun i hi j _ hj => Nat.testBit_lt_two_pow
      ((hg i hi).trans_le (Nat.pow_le_pow_right Nat.two_pos (by omega))))

/-- One selected bit in every packed word becomes a lane of zero or one. -/
lemma packF_selectBit (width size bit : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hb : bit < width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    (packF width size f >>> bit) &&& packF width size (fun _ => 1) =
      packF width size (fun i => if (f i).testBit bit then 1 else 0) := by
  rw [packF_shiftRight_and width size 1 bit f (fun _ => 1) hw (by omega) hf
    (fun _ _ => by norm_num)]
  refine packF_congr _ _ _ _ fun i _ => ?_
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (f i / 2 ^ bit) with h | h <;> simp [h]

/-- A masked left shift acts independently when the mask excludes
incoming low bits. -/
theorem masked_shiftLeft_packF (width size shift mask : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width) (hm : mask < 2 ^ width)
    (hs : ∀ j < width, j < shift → mask.testBit j = false) :
    (packF width size f <<< shift) &&& packF width size (fun _ => mask) =
      packF width size (fun i => (f i <<< shift) &&& mask) := by
  have hout : ∀ i < size, (f i <<< shift) &&& mask < 2 ^ width :=
    fun i hi => lt_of_le_of_lt Nat.and_le_right hm
  refine Nat.eq_of_testBit_eq fun k => ?_
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < width ∧ k = width * i + j :=
    ⟨k / width, k % width, Nat.mod_lt _ hw, (Nat.div_add_mod k width).symm⟩
  rw [Nat.testBit_and, Nat.testBit_shiftLeft,
    testBit_packF_at width size i j _ (fun _ _ => hm) hj,
    testBit_packF_at width size i j _ hout hj]
  by_cases hi : i < size
  · simp only [hi, if_true, Nat.testBit_and, Nat.testBit_shiftLeft]
    by_cases hb : shift ≤ j
    · rw [show width * i + j - shift = width * i + (j - shift) by omega,
        testBit_packF_at width size i (j - shift) f hf (by omega), if_pos hi]
      simp [hb, show shift ≤ width * i + j by omega]
    · rw [hs j hj (by omega)]
      simp
  · simp [hi]

end PackedDigits

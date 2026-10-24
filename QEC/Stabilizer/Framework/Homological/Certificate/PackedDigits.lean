import QEC.Stabilizer.Framework.Homological.F2Mask
import Mathlib.Data.Nat.Digits.Lemmas

namespace PackedDigits

/-- Read one fixed-width lane from a packed natural number. -/
def lane (width index value : Nat) : Nat :=
  Nat.land (Nat.shiftRight value (width * index)) (2 ^ width - 1)

/-- Bitwise lane extraction is the corresponding base-power digit. -/
theorem lane_eq_div_mod (width index value : Nat) :
    lane width index value = value / 2 ^ (width * index) % 2 ^ width := by
  simp [lane, Nat.shiftRight_eq_div_pow]

/-- Every extracted lane fits in its stated width. -/
theorem lane_lt (width index value : Nat) : lane width index value < 2 ^ width := by
  rw [lane_eq_div_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Extracting a lane commutes with bitwise intersection. -/
theorem lane_and (width index a b : Nat) :
    lane width index (a &&& b) = lane width index a &&& lane width index b := by
  simp only [lane_eq_div_mod, Nat.and_div_two_pow, Nat.and_mod_two_pow]

/-- Extracting a lane commutes with bitwise union. -/
theorem lane_or (width index a b : Nat) :
    lane width index (a ||| b) = lane width index a ||| lane width index b := by
  simp only [lane_eq_div_mod, Nat.or_div_two_pow, Nat.or_mod_two_pow]

/-- Extracting a lane commutes with exclusive-or. -/
theorem lane_xor (width index a b : Nat) :
    lane width index (a ^^^ b) = lane width index a ^^^ lane width index b := by
  simp only [lane_eq_div_mod, Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

/-- The bits of a lane are the corresponding bits of the whole table. -/
theorem testBit_lane (width index value j : Nat) :
    (lane width index value).testBit j =
      (value.testBit (width * index + j) && decide (j < width)) := by
  simp [lane, Nat.testBit_shiftRight, Bool.and_comm]

/-- A bit position lies within a lane prefix exactly when its lane index does. -/
theorem mul_add_lt_mul_iff {width i j n : Nat} (hw : 0 < width) (hj : j < width) :
    width * i + j < width * n ↔ i < n := by
  constructor
  · intro h
    by_contra hn
    have := Nat.mul_le_mul_left width (Nat.le_of_not_gt hn)
    omega
  · intro h
    nlinarith

/-- An all-ones prefix selects exactly the lanes in that prefix. -/
theorem lane_lowMask (width size i : Nat) (hw : 0 < width) :
    lane width i (2 ^ (width * size) - 1) = if i < size then 2 ^ width - 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lane, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < width
  · simp only [mul_add_lt_mul_iff hw hj]
    split <;> simp_all
  · split <;> simp_all

/-- Lane-aligned right shifts simply move lane indices. -/
theorem lane_shiftRight (width i count value : Nat) :
    lane width i (value >>> (width * count)) = lane width (i + count) value := by
  simp [lane, ← Nat.shiftRight_add, Nat.mul_add, Nat.add_comm]

/-- Lane-aligned left shifts insert zero lanes at the low end. -/
theorem lane_shiftLeft (width i count value : Nat) (hw : 0 < width) :
    lane width i (value <<< (width * count)) =
      if count ≤ i then lane width (i - count) value else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lane, Nat.testBit_shiftLeft]
  by_cases hj : j < width
  · by_cases hi : count ≤ i
    · have heq : width * i + j - width * count = width * (i - count) + j := by
        rw [Nat.mul_sub_left_distrib]
        have := Nat.mul_le_mul_left width hi
        omega
      have hle : width * count ≤ width * i + j := by
        have := Nat.mul_le_mul_left width hi
        omega
      simp [hi, hj, hle, heq, testBit_lane]
    · have hlt : width * i + j < width * count := (mul_add_lt_mul_iff hw hj).mpr (by omega)
      simp [hi, hj, show ¬ width * count ≤ width * i + j by omega]
  · split <;> simp [hj, testBit_lane]

/-- Read one digit from a list packed in base `2 ^ width`. -/
theorem lane_ofDigits (width index : Nat) (values : List Nat)
    (hvalues : ∀ v ∈ values, v < 2 ^ width) :
    lane width index (Nat.ofDigits (2 ^ width) values) = values.getD index 0 := by
  rw [lane_eq_div_mod, Nat.pow_mul,
    Nat.ofDigits_div_pow_eq_ofDigits_drop index (Nat.two_pow_pos _) values hvalues,
    Nat.ofDigits_mod_eq_head!]
  have hhead : (values.drop index).head! < 2 ^ width := by
    cases hd : values.drop index with
    | nil => simp [hd]
    | cons v vs =>
      simp only [hd, List.head!_cons]
      apply hvalues
      exact List.mem_of_mem_drop (by rw [hd]; simp)
  rw [Nat.mod_eq_of_lt hhead]
  simp [List.head!_eq_head?_getD, List.getD_eq_getElem?_getD]

/-- A positive lane width allows reconstruction from every lane. -/
theorem eq_of_lane_eq {width a b : Nat} (hw : 0 < width)
    (h : ∀ index, lane width index a = lane width index b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hx := congrArg (fun value => value.testBit (j % width)) (h (j / width))
  simpa [testBit_lane, Nat.mod_lt _ hw, Nat.div_add_mod] using hx

/-- Pack a finite table using fixed-width lanes. -/
def packF (width size : Nat) (f : Nat → Nat) : Nat :=
  Nat.ofDigits (2 ^ width) ((List.range size).map f)

/-- Reading a packed finite table recovers its entry, or zero outside the table. -/
theorem lane_packF (width size index : Nat) (f : Nat → Nat)
    (hf : ∀ i < size, f i < 2 ^ width) :
    lane width index (packF width size f) = if index < size then f index else 0 := by
  rw [packF, lane_ofDigits]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : index < size
    · simp [hi, List.getElem?_range hi]
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
      simp [hi]
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hf i (List.mem_range.mp hi)

/-- A uniform left shift acts entrywise on an algebraically packed table. -/
theorem packF_shiftLeft (width size shift : Nat) (f : Nat → Nat) :
    Nat.shiftLeft (packF width size f) shift =
      packF width size (fun i => Nat.shiftLeft (f i) shift) := by
  change packF width size f <<< shift = packF width size (fun i => f i <<< shift)
  simp only [packF, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_ofDigits]
  simp [List.map_map, Function.comp_def, Nat.mul_comm]

/-- Intersection of packed tables acts independently in every lane. -/
theorem packF_and (width size : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ width) :
    packF width size f &&& packF width size g =
      packF width size (fun i => f i &&& g i) := by
  apply eq_of_lane_eq hw
  intro i
  have hfg : ∀ i < size, f i &&& g i < 2 ^ width := by
    intro i hi
    exact lt_of_le_of_lt Nat.and_le_left (hf i hi)
  rw [lane_and, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hg,
    lane_packF _ _ _ _ hfg]
  split <;> simp_all

/-- Union of packed tables acts independently in every lane. -/
theorem packF_or (width size : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ width) :
    packF width size f ||| packF width size g =
      packF width size (fun i => f i ||| g i) := by
  apply eq_of_lane_eq hw
  intro i
  have hfg : ∀ i < size, f i ||| g i < 2 ^ width := by
    intro i hi
    exact Nat.or_lt_two_pow (hf i hi) (hg i hi)
  rw [lane_or, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hg,
    lane_packF _ _ _ _ hfg]
  split <;> simp_all

/-- Packed tables agree when all entries within the table agree. -/
theorem packF_congr (width size : Nat) (f g : Nat → Nat)
    (h : ∀ i < size, f i = g i) : packF width size f = packF width size g := by
  unfold packF
  congr 1
  exact List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))

/-- Exclusive-or of packed tables acts independently in every lane. -/
theorem packF_xor (width size : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ width) :
    packF width size f ^^^ packF width size g =
      packF width size (fun i => f i ^^^ g i) := by
  apply eq_of_lane_eq hw
  intro i
  have hfg : ∀ i < size, f i ^^^ g i < 2 ^ width := by
    intro i hi
    exact Nat.xor_lt_two_pow (hf i hi) (hg i hi)
  rw [lane_xor, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hg,
    lane_packF _ _ _ _ hfg]
  split <;> simp_all

/-- A packed Boolean mask chooses whole lanes of a packed table. -/
theorem packF_mask (width size : Nat) (f : Nat → Nat) (p : Nat → Bool)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width) :
    packF width size f &&& packF width size (fun i => if p i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if p i then f i else 0) := by
  have hm : ∀ i < size, (if p i then 2 ^ width - 1 else 0) < 2 ^ width := by
    intro i hi
    have := Nat.two_pow_pos width
    split <;> omega
  rw [packF_and _ _ _ _ hw hf hm]
  apply packF_congr
  intro i hi
  cases hp : p i <;> simp [hp, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf i hi)]

/-- A repeated low-bit mask truncates every packed lane independently. -/
theorem packF_clip (width size keep : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hk : keep ≤ width) (hf : ∀ i < size, f i < 2 ^ width) :
    packF width size f &&& packF width size (fun _ => 2 ^ keep - 1) =
      packF width size (fun i => f i % 2 ^ keep) := by
  have hm : ∀ i < size, 2 ^ keep - 1 < 2 ^ width := by
    intro i hi
    exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      (Nat.pow_le_pow_right (by omega) hk)
  rw [packF_and _ _ _ _ hw hf hm]
  apply packF_congr
  intro i hi
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- A bounded finite table fits in its allocated packed bit width. -/
theorem packF_lt (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) : packF width size f < 2 ^ (width * size) := by
  unfold packF
  rw [Nat.pow_mul]
  have hlist : ∀ v ∈ (List.range size).map f, v < 2 ^ width := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hf i (List.mem_range.mp hi)
  simpa using Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow (by omega)) hlist

/-- Algebraic addition of packed finite tables adds corresponding entries. -/
theorem packF_add (width size : Nat) (f g : Nat → Nat) :
    packF width size f + packF width size g = packF width size (fun i => f i + g i) := by
  unfold packF
  rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  simp only [List.zipWith_map, List.zipWith_self]

/-- Splitting a finite table splits its packed integer at the corresponding lane. -/
theorem packF_split (width left right : Nat) (f : Nat → Nat) :
    packF width (left + right) f = packF width left f +
      2 ^ (width * left) * packF width right (fun i => f (left + i)) := by
  simp [packF, List.range_add, List.map_append, List.map_map,
    Nat.ofDigits_append, Nat.pow_mul, Function.comp_def]

/-- Merging the two halves of a table adds matching polynomial entries. -/
theorem packF_merge (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    (packF width (size + size) f &&& (2 ^ (width * size) - 1)) +
      (packF width (size + size) f >>> (width * size)) =
      packF width size (fun i => f i + f (size + i)) := by
  rw [packF_split, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hb := packF_lt _ _ _ hw hf
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb, Nat.zero_add]
  exact packF_add _ _ _ _

/-- Duplicating a packed table introduces a freely chosen high state bit. -/
theorem packF_duplicate (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    packF width size f ||| (packF width size f <<< (width * size)) =
      packF width (size + size) (fun i => if i < size then f i else f (i - size)) := by
  rw [packF_split]
  have hlow : packF width size (fun i => if i < size then f i else f (i - size)) =
      packF width size f := by
    apply packF_congr
    intro i hi
    simp [hi]
  have hhigh : packF width size (fun i => if size + i < size then f (size + i) else f (size + i - size)) =
      packF width size f := by
    apply packF_congr
    intro i hi
    simp
  rw [hlow, hhigh, Nat.mul_comm _ (packF width size f), ← Nat.shiftLeft_eq,
    Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt (packF_lt _ _ _ hw hf), Nat.or_comm]

/-- Complementing a lane-selection mask complements the Boolean selector. -/
theorem packF_complement_mask (width size : Nat) (p : Nat → Bool) (hw : 0 < width) :
    packF width size (fun _ => 2 ^ width - 1) ^^^
      packF width size (fun i => if p i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if !(p i) then 2 ^ width - 1 else 0) := by
  have hpos := Nat.two_pow_pos width
  have hm : ∀ i < size, (if p i then 2 ^ width - 1 else 0) < 2 ^ width := by
    intro i hi
    split <;> omega
  rw [packF_xor _ _ _ _ hw (fun _ _ => by omega) hm]
  apply packF_congr
  intro i hi
  cases p i <;> simp

/-- Masked polynomial multiplication by the weight variable acts in each lane. -/
theorem packF_weight_step (width size keep shift : Nat) (f : Nat → Nat)
    (p : Nat → Bool) (hw : 0 < width) (hs : keep + shift = width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    (packF width size f &&& packF width size (fun i => if !(p i) then 2 ^ width - 1 else 0)) |||
      Nat.shiftLeft ((packF width size f &&&
        packF width size (fun i => if p i then 2 ^ width - 1 else 0)) &&&
        packF width size (fun _ => 2 ^ keep - 1)) shift =
    packF width size (fun i => if p i then Nat.shiftLeft (f i % 2 ^ keep) shift else f i) := by
  have hsel : ∀ i < size, (if p i then f i else 0) < 2 ^ width := by
    intro i hi
    split
    · exact hf i hi
    · exact Nat.two_pow_pos _
  have hnot : ∀ i < size, (if !(p i) then f i else 0) < 2 ^ width := by
    intro i hi
    split
    · exact hf i hi
    · exact Nat.two_pow_pos _
  have hshift : ∀ i < size,
      Nat.shiftLeft ((if p i then f i else 0) % 2 ^ keep) shift < 2 ^ width := by
    intro i hi
    have h := Nat.shiftLeft_lt (m := shift) (Nat.mod_lt (if p i then f i else 0) (Nat.two_pow_pos keep))
    simpa [hs] using h
  rw [packF_mask _ _ _ _ hw hf, packF_mask _ _ _ _ hw hf,
    packF_clip _ _ _ _ hw (by omega) hsel, packF_shiftLeft,
    packF_or _ _ _ _ hw hnot hshift]
  apply packF_congr
  intro i hi
  cases p i <;> simp [Nat.shiftLeft]

/-- Preclipping before a polynomial shift is reduction modulo the lane capacity. -/
theorem clip_shift_eq_mod (value keep shift : Nat) :
    Nat.shiftLeft (value % 2 ^ keep) shift =
      (value * 2 ^ shift) % 2 ^ (keep + shift) := by
  change (value % 2 ^ keep) <<< shift = (value * 2 ^ shift) % 2 ^ (keep + shift)
  rw [Nat.shiftLeft_eq, pow_add]
  simpa [Nat.mul_comm] using (Nat.mul_mod_mul_left (2 ^ shift) value (2 ^ keep)).symm

/-- Concatenating two lists concatenates their packed bit blocks. -/
theorem pack_append (width : Nat) (left right : List Nat)
    (hleft : ∀ v ∈ left, v < 2 ^ width) :
    Nat.ofDigits (2 ^ width) (left ++ right) =
      Nat.ofDigits (2 ^ width) left |||
        Nat.shiftLeft (Nat.ofDigits (2 ^ width) right) (width * left.length) := by
  by_cases hw : width = 0
  · subst width
    have hl : ∀ v ∈ left, v = 0 := by
      intro v hv
      have := hleft v hv
      simpa using this
    have hz : Nat.ofDigits 1 left = 0 := by
      rw [Nat.ofDigits_one]
      exact List.sum_eq_zero hl
    simp [Nat.ofDigits_append, hz]
  · have hlt : Nat.ofDigits (2 ^ width) left < 2 ^ (width * left.length) := by
      rw [Nat.pow_mul]
      exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow (by omega)) hleft
    rw [Nat.ofDigits_append, ← Nat.pow_mul, Nat.mul_comm _ (Nat.ofDigits _ right),
      ← Nat.shiftLeft_eq, Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.or_comm]
    rfl

/-- Forgetting the high binary state bit adds corresponding packed polynomial lanes. -/
theorem pack_merge_halves (width : Nat) (left right : List Nat)
    (hleft : ∀ v ∈ left, v < 2 ^ width) (hlen : left.length = right.length) :
    let packed := Nat.ofDigits (2 ^ width) (left ++ right)
    Nat.land packed (2 ^ (width * left.length) - 1) +
      Nat.shiftRight packed (width * left.length) =
      Nat.ofDigits (2 ^ width) (left.zipWith (· + ·) right) := by
  dsimp
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.ofDigits_append, ← Nat.pow_mul]
  have hb : Nat.ofDigits (2 ^ width) left < 2 ^ (width * left.length) := by
    by_cases hw : width = 0
    · subst width
      have hz : Nat.ofDigits 1 left = 0 := by
        rw [Nat.ofDigits_one]
        apply List.sum_eq_zero
        intro v hv
        have := hleft v hv
        simpa using this
      simpa [hz]
    · rw [Nat.pow_mul]
      exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow (by omega)) hleft
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb, Nat.zero_add]
  exact Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq hlen

/-- Duplicate a finite bit block. -/
def doubleBlock (value width : Nat) : Nat := value ||| value <<< width

/-- A doubled block occupies precisely twice the original bit capacity. -/
theorem doubleBlock_lt (value width : Nat) (h : value < 2 ^ width) :
    doubleBlock value width < 2 ^ (2 * width) := by
  simpa [doubleBlock, Nat.two_mul, Nat.or_comm] using Nat.append_lt h h

/-- A doubled block reads either copy of its original bit pattern. -/
theorem testBit_doubleBlock (value width j : Nat) (h : value < 2 ^ width) :
    (doubleBlock value width).testBit j =
      (decide (j < 2 * width) && value.testBit (j % width)) := by
  by_cases hj : j < width
  · simp [doubleBlock, Nat.testBit_shiftLeft, Nat.mod_eq_of_lt hj,
      show ¬ width ≤ j by omega, show j < 2 * width by omega]
  · have hjw : width ≤ j := by omega
    have hvj : value.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hjw))
    by_cases hj2 : j < 2 * width
    · have hm : j % width = j - width := by
        rw [Nat.mod_eq_sub_mod hjw, Nat.mod_eq_of_lt (by omega)]
      simp [doubleBlock, Nat.testBit_shiftLeft, hvj, hjw, hj2, hm]
    · have hvjw : value.testBit (j - width) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h
          (Nat.pow_le_pow_right (by omega) (by omega : width ≤ j - width)))
      simp [doubleBlock, Nat.testBit_shiftLeft, hvj, hjw, hj2, hvjw]

/-- Repeat a finite bit block by successive doubling. -/
def repeatBlock : Nat → Nat → Nat → Nat
  | value, _, 0 => value
  | value, width, e + 1 => repeatBlock (doubleBlock value width) (2 * width) e

/-- Repeated blocks retain their fixed-width bit pattern. -/
theorem testBit_repeatBlock (value width e j : Nat) (hw : 0 < width)
    (hv : value < 2 ^ width) :
    (repeatBlock value width e).testBit j =
      (decide (j < width * 2 ^ e) && value.testBit (j % width)) := by
  induction e generalizing value width with
  | zero =>
    simp only [repeatBlock, pow_zero, Nat.mul_one]
    by_cases hj : j < width
    · simp [hj, Nat.mod_eq_of_lt hj]
    · have hz : value.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
          (Nat.pow_le_pow_right (by omega) (by omega : width ≤ j)))
      simp [hj, hz]
  | succ e ih =>
    rw [repeatBlock, ih _ _ (by omega) (doubleBlock_lt _ _ hv),
      testBit_doubleBlock _ _ _ hv]
    have hm : (j % (2 * width)) % width = j % width :=
      Nat.mod_mod_of_dvd j (by simp)
    simp only [Nat.mod_lt _ (by omega : 0 < 2 * width), decide_true, Bool.true_and, hm]
    simp [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Every lane of a repeated block is the original block. -/
theorem lane_repeatBlock (value width e i : Nat) (hw : 0 < width)
    (hv : value < 2 ^ width) :
    lane width i (repeatBlock value width e) = if i < 2 ^ e then value else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lane, testBit_repeatBlock _ _ _ _ hw hv]
  by_cases hj : j < width
  · have hmod : (width * i + j) % width = j := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
    rw [hmod]
    by_cases hi : i < 2 ^ e
    · have htotal : width * i + j < width * 2 ^ e := by
        nlinarith
      simp [hi, hj, htotal]
    · have htotal : ¬ width * i + j < width * 2 ^ e := by
        have := Nat.mul_le_mul_left width (Nat.le_of_not_gt hi)
        omega
      simp [hi, hj, htotal]
  · have hz : value.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
        (Nat.pow_le_pow_right (by omega) (by omega : width ≤ j)))
    split <;> simp [hj, hz]

/-- Repeated bit blocks coincide with the mathematical constant table packing. -/
theorem repeatBlock_eq_packF (value width e : Nat) (hw : 0 < width)
    (hv : value < 2 ^ width) :
    repeatBlock value width e = packF width (2 ^ e) (fun _ => value) := by
  apply eq_of_lane_eq hw
  intro i
  rw [lane_repeatBlock _ _ _ _ hw hv, lane_packF _ _ _ _ (fun _ _ => hv)]

/-- Repeating an all-ones block yields an all-ones block of the combined width. -/
theorem repeatBlock_lowMask (width e : Nat) (hw : 0 < width) :
    repeatBlock (2 ^ width - 1) width e = 2 ^ (width * 2 ^ e) - 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_repeatBlock _ _ _ _ hw (Nat.sub_lt (Nat.two_pow_pos _) (by omega))]
  simp [Nat.mod_lt _ hw]

/-- Modulo a whole number of lanes preserves the bit offset inside a lane. -/
theorem mul_add_mod_mul (width size i j : Nat) (hw : 0 < width) (hs : 0 < size)
    (hj : j < width) :
    (width * i + j) % (width * size) = width * (i % size) + j := by
  have hr := Nat.mod_lt i hs
  have hbound : width * (i % size) + j < width * size := (mul_add_lt_mul_iff hw hj).mpr hr
  have heq : width * i + j = width * (i % size) + j + (width * size) * (i / size) := by
    have hdiv := Nat.div_add_mod i size
    nlinarith
  rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]

/-- Repeating a wider block repeats its constituent lanes periodically. -/
theorem lane_repeatBlock_wide (value width size e i : Nat) (hw : 0 < width)
    (hs : 0 < size) (hv : value < 2 ^ (width * size)) :
    lane width i (repeatBlock value (width * size) e) =
      if i < size * 2 ^ e then lane width (i % size) value else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lane, testBit_repeatBlock _ _ _ _ (Nat.mul_pos hw hs) hv]
  by_cases hj : j < width
  · rw [mul_add_mod_mul _ _ _ _ hw hs hj, Nat.mul_assoc]
    simp only [mul_add_lt_mul_iff hw hj]
    split <;> simp_all [testBit_lane]
  · split <;> simp [hj, testBit_lane]

/-- A zero bit is exactly the lower half of its periodic residue block. -/
theorem not_testBit_eq_decide_mod_lt (i p : Nat) :
    (!(i.testBit p)) = decide (i % 2 ^ (p + 1) < 2 ^ p) := by
  have hdiv : i % 2 ^ (p + 1) / 2 ^ p = i / 2 ^ p % 2 := by
    rw [pow_succ, Nat.mod_mul_right_div_self]
  have heq : i % 2 ^ (p + 1) < 2 ^ p ↔ i / 2 ^ p % 2 = 0 := by
    rw [← hdiv, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  simp only [Nat.testBit_eq_decide_div_mod_eq, heq]
  by_cases hz : i / 2 ^ p % 2 = 0
  · simp [hz]
  · have ho : i / 2 ^ p % 2 = 1 := by
      have := Nat.mod_lt (i / 2 ^ p) (by decide : 0 < 2)
      omega
    simp [ho]

/-- Periodic mask that selects states whose chosen binary coordinate is zero. -/
def bitZeroMask (width bits position : Nat) : Nat :=
  repeatBlock (2 ^ (width * 2 ^ position) - 1) (width * 2 ^ (position + 1))
    (bits - position - 1)

/-- The efficient periodic state mask selects precisely the corresponding zero bit. -/
theorem bitZeroMask_eq_packF (width bits position : Nat) (hw : 0 < width)
    (hp : position < bits) :
    bitZeroMask width bits position =
      packF width (2 ^ bits) (fun i => if !(i.testBit position) then 2 ^ width - 1 else 0) := by
  have hpow : 2 ^ position ≤ 2 ^ (position + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hv : 2 ^ (width * 2 ^ position) - 1 < 2 ^ (width * 2 ^ (position + 1)) := by
    exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left width hpow))
  have hsize : 2 ^ (position + 1) * 2 ^ (bits - position - 1) = 2 ^ bits := by
    rw [← pow_add]
    congr 1
    omega
  have hmask : ∀ i < 2 ^ bits,
      (if !(i.testBit position) then 2 ^ width - 1 else 0) < 2 ^ width := by
    intro i hi
    have := Nat.two_pow_pos width
    split <;> omega
  apply eq_of_lane_eq hw
  intro i
  rw [bitZeroMask, lane_repeatBlock_wide _ _ _ _ _ hw (Nat.two_pow_pos _) hv,
    hsize, lane_lowMask _ _ _ hw, lane_packF _ _ _ _ hmask,
    not_testBit_eq_decide_mod_lt]
  split <;> simp_all

/-- Exclusive-or of Boolean lane masks corresponds to exclusive-or of selectors. -/
theorem packF_mask_xor (width size : Nat) (p q : Nat → Bool) (hw : 0 < width) :
    packF width size (fun i => if p i then 2 ^ width - 1 else 0) ^^^
      packF width size (fun i => if q i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if p i ^^ q i then 2 ^ width - 1 else 0) := by
  have hbound (p : Nat → Bool) : ∀ i < size,
      (if p i then 2 ^ width - 1 else 0) < 2 ^ width := by
    intro i hi
    have := Nat.two_pow_pos width
    split <;> omega
  rw [packF_xor _ _ _ _ hw (hbound p) (hbound q)]
  apply packF_congr
  intro i hi
  cases p i <;> cases q i <;> simp

/-- Intersection of Boolean lane masks corresponds to conjunction of selectors. -/
theorem packF_mask_and (width size : Nat) (p q : Nat → Bool) (hw : 0 < width) :
    packF width size (fun i => if p i then 2 ^ width - 1 else 0) &&&
      packF width size (fun i => if q i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if p i && q i then 2 ^ width - 1 else 0) := by
  have hbound (p : Nat → Bool) : ∀ i < size,
      (if p i then 2 ^ width - 1 else 0) < 2 ^ width := by
    intro i hi
    have := Nat.two_pow_pos width
    split <;> omega
  rw [packF_and _ _ _ _ hw (hbound p) (hbound q)]
  apply packF_congr
  intro i hi
  cases p i <;> cases q i <;> simp

/-- A shorter all-ones prefix is a lane-selection mask in a larger table. -/
theorem prefixMask_eq_packF (width size count : Nat) (hw : 0 < width) (hp : count ≤ size) :
    2 ^ (width * count) - 1 =
      packF width size (fun i => if i < count then 2 ^ width - 1 else 0) := by
  have hb : ∀ i < size, (if i < count then 2 ^ width - 1 else 0) < 2 ^ width := by
    intro i hi
    have := Nat.two_pow_pos width
    split <;> omega
  apply eq_of_lane_eq hw
  intro i
  rw [lane_lowMask _ _ _ hw, lane_packF _ _ _ _ hb]
  split_ifs <;> omega

/-- Folding efficient bit masks computes the parity selector in every table lane. -/
theorem fold_bitZeroMask_eq_packF (width bits : Nat) (ps : List Nat)
    (initial : Nat → Bool) (hw : 0 < width) (hp : ∀ p ∈ ps, p < bits) :
    ps.foldl (fun acc p => acc ^^^ bitZeroMask width bits p)
      (packF width (2 ^ bits) (fun i => if initial i then 2 ^ width - 1 else 0)) =
    packF width (2 ^ bits)
      (fun i => if ps.foldl (fun acc p => acc ^^ !(i.testBit p)) (initial i)
        then 2 ^ width - 1 else 0) := by
  induction ps generalizing initial with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons, bitZeroMask_eq_packF _ _ _ hw (hp p (by simp)),
      packF_mask_xor _ _ _ _ hw, ih _ (fun p hp' => hp p (by simp [hp']))]
    rfl

/-- The lane value produced by a three-part stationary/upward/downward transport. -/
def transportedValue (size delta i : Nat) (f : Nat → Nat) (up down : Nat → Bool) : Nat :=
  (if !(up i ^^ down i) then f i else 0) |||
    (if delta ≤ i then if i - delta < size then if up (i - delta) then f (i - delta) else 0 else 0 else 0) |||
    (if i + delta < size then if down (i + delta) then f (i + delta) else 0 else 0)

/-- Disjoint moving lane subsets implement their scalar source-index transport. -/
theorem packF_transport (width size delta : Nat) (f source : Nat → Nat)
    (up down : Nat → Bool) (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width)
    (hsource : ∀ i < size, source i < size)
    (hup : ∀ i < size, up i = true → i + delta < size)
    (hmove : ∀ i < size, transportedValue size delta i f up down = f (source i)) :
    packF width size (fun i => if !(up i ^^ down i) then f i else 0) |||
      (packF width size (fun i => if up i then f i else 0) <<< (width * delta)) |||
      (packF width size (fun i => if down i then f i else 0) >>> (width * delta)) =
      packF width size (fun i => f (source i)) := by
  have hsel (p : Nat → Bool) : ∀ i < size, (if p i then f i else 0) < 2 ^ width := by
    intro i hi
    split
    · exact hf i hi
    · exact Nat.two_pow_pos _
  apply eq_of_lane_eq hw
  intro i
  rw [lane_or, lane_or, lane_shiftLeft _ _ _ _ hw, lane_shiftRight,
    lane_packF _ _ _ _ (hsel (fun i => !(up i ^^ down i))),
    lane_packF _ _ _ _ (hsel up), lane_packF _ _ _ _ (hsel down),
    lane_packF _ _ _ _ (fun i hi => hf _ (hsource i hi))]
  by_cases hi : i < size
  · simpa [hi, transportedValue] using hmove i hi
  · have hhigh : ¬ i + delta < size := by omega
    have hlow : (if delta ≤ i then
        if i - delta < size then if up (i - delta) then f (i - delta) else 0 else 0 else 0) = 0 := by
      split_ifs with hd hr hu
      · have := hup (i - delta) hr hu
        omega
      all_goals rfl
    simp [hi, hhigh, hlow]

/-- A scalar certificate identifies the unique source of every transported lane. -/
def checkTransport (size delta i : Nat) (up down : Nat → Bool) (source : Nat → Nat) : Bool :=
  let stay := !(up i ^^ down i)
  let fromLow := decide (delta ≤ i) && decide (i - delta < size) && up (i - delta)
  let fromHigh := decide (i + delta < size) && down (i + delta)
  decide (source i < size) && (!(up i) || decide (i + delta < size)) &&
    ((stay && !fromLow && !fromHigh && decide (source i = i)) ||
     (!stay && fromLow && !fromHigh && decide (source i = i - delta)) ||
     (!stay && !fromLow && fromHigh && decide (source i = i + delta)))

/-- Successful scalar transport certificates bound every selected source index. -/
theorem checkTransport_source {size delta i : Nat} {up down : Nat → Bool} {source : Nat → Nat}
    (h : checkTransport size delta i up down source = true) : source i < size := by
  simp only [checkTransport, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- A successful scalar certificate keeps every upward-moving lane within the table. -/
theorem checkTransport_up {size delta i : Nat} {up down : Nat → Bool} {source : Nat → Nat}
    (h : checkTransport size delta i up down source = true) (hu : up i = true) : i + delta < size := by
  have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  simpa [hu] using hh

/-- A one-of-three selector certificate identifies its selected value. -/
theorem transportValues_of_certificate (stay low high : Bool) (source i delta : Nat)
    (f : Nat → Nat)
    (h : ((stay && !low && !high && decide (source = i)) ||
      (!stay && low && !high && decide (source = i - delta)) ||
      (!stay && !low && high && decide (source = i + delta))) = true) :
    (if stay then f i else 0) ||| (if low then f (i - delta) else 0) |||
      (if high then f (i + delta) else 0) = f source := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h <;> simp_all

/-- Scalar transport certificates identify each lane value for arbitrary table contents. -/
theorem checkTransport_value {size delta i : Nat} {up down : Nat → Bool} {source : Nat → Nat}
    (h : checkTransport size delta i up down source = true) (f : Nat → Nat) :
    transportedValue size delta i f up down = f (source i) := by
  have hc := (Bool.and_eq_true_iff.mp h).2
  have ht := transportValues_of_certificate (!(up i ^^ down i))
    (decide (delta ≤ i) && decide (i - delta < size) && up (i - delta))
    (decide (i + delta < size) && down (i + delta)) (source i) i delta f hc
  simpa [transportedValue, Bool.and_eq_true, ite_and] using ht

/-- An all-ones prefix is the constant all-ones finite lane table. -/
theorem lowMask_eq_packF (width size : Nat) (hw : 0 < width) :
    2 ^ (width * size) - 1 = packF width size (fun _ => 2 ^ width - 1) := by
  apply eq_of_lane_eq hw
  intro i
  rw [lane_lowMask _ _ _ hw,
    lane_packF _ _ _ _ (fun _ _ => Nat.sub_lt (Nat.two_pow_pos _) (by omega))]

/-- Kernel-checked scalar transport laws certify the three-mask packed permutation. -/
theorem packF_swap_of_check (width size delta : Nat) (f source : Nat → Nat)
    (up down : Nat → Bool) (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width)
    (hcheck : ∀ i < size, checkTransport size delta i up down source = true) :
    (packF width size f &&& ((2 ^ (width * size) - 1) ^^^
      packF width size (fun i => if up i then 2 ^ width - 1 else 0) ^^^
      packF width size (fun i => if down i then 2 ^ width - 1 else 0))) |||
    ((packF width size f &&& packF width size (fun i => if up i then 2 ^ width - 1 else 0))
      <<< (width * delta)) |||
    ((packF width size f &&& packF width size (fun i => if down i then 2 ^ width - 1 else 0))
      >>> (width * delta)) = packF width size (fun i => f (source i)) := by
  rw [lowMask_eq_packF _ _ hw, Nat.xor_assoc,
    packF_mask_xor _ _ _ _ hw, packF_complement_mask _ _ _ hw,
    packF_mask _ _ _ _ hw hf, packF_mask _ _ _ _ hw hf, packF_mask _ _ _ _ hw hf]
  exact packF_transport _ _ _ _ _ _ _ hw hf
    (fun i hi => checkTransport_source (hcheck i hi))
    (fun i hi hu => checkTransport_up (hcheck i hi) hu)
    (fun i hi => checkTransport_value (hcheck i hi) f)

/-- A packed polynomial has a fixed number of coefficients, all below a common bound. -/
def BoundedPolynomial (slot degree bound value : Nat) : Prop :=
  ∃ coefficients : List Nat, coefficients.length = degree + 1 ∧
    (∀ c ∈ coefficients, c ≤ bound) ∧ Nat.ofDigits (2 ^ slot) coefficients = value

/-- A bounded polynomial fits in its allocated lane whenever its coefficients fit their slots. -/
theorem BoundedPolynomial.lt {slot degree bound value : Nat}
    (h : BoundedPolynomial slot degree bound value) (hs : 0 < slot) (hb : bound < 2 ^ slot) :
    value < 2 ^ (slot * (degree + 1)) := by
  obtain ⟨coefficients, hlen, hbound, rfl⟩ := h
  rw [Nat.pow_mul, ← hlen]
  exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow (by omega))
    (fun c hc => lt_of_le_of_lt (hbound c hc) hb)

/-- The zero polynomial satisfies every nonnegative coefficient bound. -/
theorem BoundedPolynomial.zero (slot degree bound : Nat) :
    BoundedPolynomial slot degree bound 0 := by
  refine ⟨List.replicate (degree + 1) 0, by simp, ?_, by simp⟩
  intro c hc
  simp only [List.mem_replicate] at hc
  omega

/-- The initial constant polynomial has coefficients at most one. -/
theorem BoundedPolynomial.one (slot degree : Nat) :
    BoundedPolynomial slot degree 1 1 := by
  refine ⟨1 :: List.replicate degree 0, by simp, ?_, by simp [Nat.ofDigits_cons]⟩
  intro c hc
  simp only [List.mem_cons, List.mem_replicate] at hc
  omega

/-- Increasing a coefficient bound preserves the bounded-polynomial predicate. -/
theorem BoundedPolynomial.mono {slot degree bound bound' value : Nat}
    (h : BoundedPolynomial slot degree bound value) (hb : bound ≤ bound') :
    BoundedPolynomial slot degree bound' value := by
  obtain ⟨coefficients, hlen, hbound, hvalue⟩ := h
  exact ⟨coefficients, hlen, fun c hc => (hbound c hc).trans hb, hvalue⟩

/-- Adding packed polynomials adds their coefficient bounds without assuming a carry bound. -/
theorem BoundedPolynomial.add {slot degree bound bound' value value' : Nat}
    (h : BoundedPolynomial slot degree bound value)
    (h' : BoundedPolynomial slot degree bound' value') :
    BoundedPolynomial slot degree (bound + bound') (value + value') := by
  obtain ⟨a, ha, hca, rfl⟩ := h
  obtain ⟨b, hb, hcb, rfl⟩ := h'
  refine ⟨a.zipWith (· + ·) b, by simp [ha, hb], ?_, ?_⟩
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    simp only [List.getElem_zipWith]
    exact Nat.add_le_add (hca _ (List.getElem_mem ..)) (hcb _ (List.getElem_mem ..))
  · exact (Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (ha.trans hb.symm)).symm

/-- Shifting and truncating a polynomial preserves its coefficient bound. -/
theorem BoundedPolynomial.shift {slot degree bound value : Nat}
    (h : BoundedPolynomial slot degree bound value) (hb : bound < 2 ^ slot) :
    BoundedPolynomial slot degree bound ((value * 2 ^ slot) % 2 ^ (slot * (degree + 1))) := by
  obtain ⟨coefficients, hlen, hbound, rfl⟩ := h
  have hcoeff : ∀ c ∈ 0 :: coefficients, c < 2 ^ slot := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.two_pow_pos _
    · exact lt_of_le_of_lt (hbound c hc) hb
  refine ⟨(0 :: coefficients).take (degree + 1), by simp [hlen], ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp (List.mem_of_mem_take hc) with rfl | hc
    · omega
    · exact hbound c hc
  · rw [Nat.pow_mul, ← Nat.ofDigits_mod_pow_eq_ofDigits_take (degree + 1)
      (Nat.two_pow_pos slot) (0 :: coefficients) hcoeff]
    simp [Nat.ofDigits_cons, Nat.mul_comm]

#print axioms BoundedPolynomial.add
#print axioms BoundedPolynomial.shift
#print axioms bitZeroMask_eq_packF
#print axioms lane_shiftLeft
#print axioms lane_repeatBlock_wide
#print axioms lane_repeatBlock
#print axioms repeatBlock_eq_packF
#print axioms repeatBlock_lowMask
#print axioms testBit_repeatBlock
#print axioms lane_ofDigits
#print axioms pack_append
#print axioms pack_merge_halves
#print axioms testBit_doubleBlock
end PackedDigits

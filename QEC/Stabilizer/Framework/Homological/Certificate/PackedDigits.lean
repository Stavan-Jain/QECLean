import QEC.Stabilizer.Framework.Homological.F2Mask
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Tables packed into fixed-width lanes of a natural number

A table of `size` natural numbers, each below `2 ^ width`, is packed into one
natural number by giving entry `i` the `width` bits starting at position
`width * i` (its *lane*). A single big-number operation on the packed number
then acts on every entry at once, which is what makes table-sized checks cheap
for the kernel. This file relates the packed operations to the entrywise ones.

* `lane width i v` reads lane `i` of `v`, and `packF width size f` packs the
  table `f 0, …, f (size - 1)`; `lane_packF` reads an entry back, and a number
  is determined by its lanes (`eq_of_lane_eq`).
* Bitwise operations, arithmetic and lane-aligned shifts act lane by lane:
  `packF_and`, `packF_or`, `packF_xor`, `packF_add`, `packF_sub`, `packF_mul`,
  `packF_shift_left`, `lane_shiftLeft`, `lane_shiftRight`. `packF_split`,
  `packF_append` and `packF_merge` cut a table in two, concatenate two tables,
  and add the two halves of a table.
* Lane selection: `packF_mask` keeps the lanes chosen by a Boolean selector,
  `packF_clip` truncates every lane, and `packF_weight_step` multiplies the
  selected lanes by a power of two.
* `repeatBlock` builds a periodic constant by repeated doubling
  (`repeatBlock_eq_packF`), and `bitZeroMask` uses it for the mask selecting
  the lanes whose index has a given binary digit equal to `0`
  (`bitZeroMask_eq_packF`, `fold_bitZeroMask_eq_packF`).
* `packF_swap_of_check` permutes the lanes of a table by moving two sets of
  lanes a fixed distance up and down; the scalar check `checkTransport`
  certifies the permutation one lane at a time.
* `BoundedPolynomial slot degree bound v` says that `v` packs `degree + 1`
  coefficients, each at most `bound`, into slots of `slot` bits. It is
  preserved by addition (`BoundedPolynomial.add`) and by multiplication by the
  variable followed by truncation (`BoundedPolynomial.shift`).
-/

namespace PackedDigits

/-! ## Lanes -/

/-- Lane `index` of `value`: the `width` bits starting at position
`width * index`. -/
def lane (width index value : Nat) : Nat :=
  Nat.land (Nat.shiftRight value (width * index)) (2 ^ width - 1)

/-- A lane is the corresponding digit in base `2 ^ width`. -/
lemma lane_eq_div_mod (width index value : Nat) :
    lane width index value = value / 2 ^ (width * index) % 2 ^ width := by
  simp [lane, Nat.shiftRight_eq_div_pow]

/-- Every extracted lane fits in its stated width. -/
lemma lane_lt (width index value : Nat) : lane width index value < 2 ^ width := by
  rw [lane_eq_div_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Extracting a lane commutes with bitwise intersection. -/
lemma lane_and (width index a b : Nat) :
    lane width index (a &&& b) = lane width index a &&& lane width index b := by
  simp only [lane_eq_div_mod, Nat.and_div_two_pow, Nat.and_mod_two_pow]

/-- Extracting a lane commutes with bitwise union. -/
lemma lane_or (width index a b : Nat) :
    lane width index (a ||| b) = lane width index a ||| lane width index b := by
  simp only [lane_eq_div_mod, Nat.or_div_two_pow, Nat.or_mod_two_pow]

/-- Extracting a lane commutes with exclusive-or. -/
lemma lane_xor (width index a b : Nat) :
    lane width index (a ^^^ b) = lane width index a ^^^ lane width index b := by
  simp only [lane_eq_div_mod, Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

/-- The bits of a lane are the corresponding bits of the whole table. -/
lemma testBit_lane (width index value j : Nat) :
    (lane width index value).testBit j =
      (value.testBit (width * index + j) && decide (j < width)) := by
  simp [lane, Nat.testBit_shiftRight, Bool.and_comm]

/-- A bit position lies within a lane prefix exactly when its lane index
does. -/
lemma mul_add_lt_mul_iff {width i j n : Nat} (hj : j < width) :
    width * i + j < width * n ↔ i < n := by
  rw [Nat.mul_comm width n, ← Nat.div_lt_iff_lt_mul (by omega), Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt hj, Nat.add_zero]

/-- Modulo a whole number of lanes preserves the bit offset inside a lane. -/
lemma mul_add_mod_mul (width size i j : Nat) (hj : j < width) :
    (width * i + j) % (width * size) = width * (i % size) + j := by
  rw [Nat.mod_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt hj, Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt hj, Nat.add_zero, Nat.add_comm]

/-- A number below `2 ^ width` has no set bit at position `width` or above. -/
private lemma testBit_eq_false_of_lt {value width j : Nat} (hv : value < 2 ^ width)
    (hj : width ≤ j) : value.testBit j = false :=
  Nat.testBit_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right Nat.two_pos hj))

/-- A lane of `width` bits has room for a value below `2 ^ bits` and one more
bit whenever `bits < width`. -/
lemma two_pow_mul_two_le {bits width : Nat} (h : bits < width) :
    2 ^ bits * 2 ≤ 2 ^ width := by
  rw [← pow_succ]
  exact Nat.pow_le_pow_right Nat.two_pos h

/-- An all-ones prefix selects exactly the lanes in that prefix. -/
lemma lane_lowMask (width size i : Nat) :
    lane width i (2 ^ (width * size) - 1) = if i < size then 2 ^ width - 1 else 0 := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_lane, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < width
  · simp only [mul_add_lt_mul_iff hj]
    split <;> simp_all
  · split <;> simp_all

/-- Lane-aligned right shifts simply move lane indices. -/
lemma lane_shiftRight (width i count value : Nat) :
    lane width i (value >>> (width * count)) = lane width (i + count) value := by
  simp [lane, ← Nat.shiftRight_add, Nat.mul_add, Nat.add_comm]

/-- Lane-aligned left shifts insert zero lanes at the low end. -/
lemma lane_shiftLeft (width i count value : Nat) :
    lane width i (value <<< (width * count)) =
      if count ≤ i then lane width (i - count) value else 0 := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_lane, Nat.testBit_shiftLeft]
  by_cases hj : j < width
  · by_cases hi : count ≤ i
    · have hle := Nat.mul_le_mul_left width hi
      have heq : width * i + j - width * count = width * (i - count) + j := by
        rw [Nat.mul_sub_left_distrib]
        omega
      simp [hi, hj, show width * count ≤ width * i + j by omega, heq, testBit_lane]
    · have hlt : width * i + j < width * count := (mul_add_lt_mul_iff hj).mpr (by omega)
      simp [hi, hj, show ¬ width * count ≤ width * i + j by omega]
  · split <;> simp [hj, testBit_lane]

/-- Lane `index` of a list packed in base `2 ^ width` is its entry `index`. -/
lemma lane_ofDigits (width index : Nat) (values : List Nat)
    (hvalues : ∀ v ∈ values, v < 2 ^ width) :
    lane width index (Nat.ofDigits (2 ^ width) values) = values.getD index 0 := by
  rw [lane_eq_div_mod, Nat.pow_mul,
    Nat.ofDigits_div_pow_eq_ofDigits_drop index (Nat.two_pow_pos _) values hvalues,
    Nat.ofDigits_mod_eq_head!]
  have hhead : (values.drop index).head! < 2 ^ width := by
    cases hd : values.drop index with
    | nil => simp
    | cons v vs => exact hvalues _ (List.mem_of_mem_drop (hd ▸ List.mem_cons_self))
  rw [Nat.mod_eq_of_lt hhead]
  simp [List.head!_eq_head?_getD, List.getD_eq_getElem?_getD]

/-- For a positive lane width, two numbers with the same lanes are equal. -/
theorem eq_of_lane_eq {width a b : Nat} (hw : 0 < width)
    (h : ∀ index, lane width index a = lane width index b) : a = b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  have hx := congrArg (fun value => value.testBit (j % width)) (h (j / width))
  simpa [testBit_lane, Nat.mod_lt _ hw, Nat.div_add_mod] using hx

/-! ## Packed tables -/

/-- The table `f 0, …, f (size - 1)` packed into lanes of `width` bits: entry
`i` occupies lane `i`. -/
def packF (width size : Nat) (f : Nat → Nat) : Nat :=
  Nat.ofDigits (2 ^ width) ((List.range size).map f)

/-- Reading a packed finite table recovers its entry, or zero outside the
table. -/
theorem lane_packF (width size index : Nat) (f : Nat → Nat)
    (hf : ∀ i < size, f i < 2 ^ width) :
    lane width index (packF width size f) = if index < size then f index else 0 := by
  rw [packF, lane_ofDigits _ _ _ (List.forall_mem_map.mpr fun i hi => hf i (List.mem_range.mp hi))]
  by_cases hi : index < size <;> simp [List.getD_eq_getElem?_getD, hi]

/-- Packed tables agree when all entries within the table agree. -/
lemma packF_congr (width size : Nat) (f g : Nat → Nat)
    (h : ∀ i < size, f i = g i) : packF width size f = packF width size g :=
  congrArg (Nat.ofDigits (2 ^ width))
    (List.map_congr_left fun i hi => h i (List.mem_range.mp hi))

/-- A bounded finite table fits in its allocated packed bit width. -/
lemma packF_lt (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) : packF width size f < 2 ^ (width * size) := by
  have h := Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow hw.ne')
    (List.forall_mem_map.mpr fun i hi => hf i (List.mem_range.mp hi))
  simpa [Nat.pow_mul] using h

/-- A bit within a packed table lane is the same bit of the table entry. -/
lemma testBit_packF_at (width size index bit : Nat) (f : Nat → Nat)
    (hf : ∀ j < size, f j < 2 ^ width) (hb : bit < width) :
    (packF width size f).testBit (width * index + bit) =
      if index < size then (f index).testBit bit else false := by
  have h := testBit_lane width index (packF width size f) bit
  rw [lane_packF _ _ _ _ hf] at h
  by_cases hi : index < size <;> simpa [hb, hi] using h.symm

/-- A bounded packed integer is recovered from all of its lanes. -/
lemma packF_lanes (width size value : Nat) (hw : 0 < width)
    (hv : value < 2 ^ (width * size)) :
    packF width size (fun i => lane width i value) = value := by
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_packF _ _ _ _ (fun _ _ => lane_lt _ _ _)]
  by_cases hi : i < size
  · simp [hi]
  · have hlt : value < 2 ^ (width * i) := lt_of_lt_of_le hv
      (Nat.pow_le_pow_right Nat.two_pos (Nat.mul_le_mul_left width (by omega)))
    simp [hi, lane_eq_div_mod, Nat.div_eq_of_lt hlt]

/-- A uniform left shift acts entrywise on a packed table. -/
lemma packF_shift_left (width size shift : Nat) (f : Nat → Nat) :
    packF width size f <<< shift = packF width size (fun i => f i <<< shift) := by
  simp only [packF, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_ofDigits]
  simp [List.map_map, Function.comp_def, Nat.mul_comm]

/-- `packF_shift_left` stated with the raw `Nat.shiftLeft`, the spelling used
in kernel-evaluated definitions. -/
lemma packF_shiftLeft (width size shift : Nat) (f : Nat → Nat) :
    Nat.shiftLeft (packF width size f) shift =
      packF width size (fun i => Nat.shiftLeft (f i) shift) :=
  packF_shift_left width size shift f

/-- Intersection of packed tables acts independently in every lane. -/
lemma packF_and (width size : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ width) :
    packF width size f &&& packF width size g =
      packF width size (fun i => f i &&& g i) := by
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_and, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hg,
    lane_packF _ _ _ _ fun i hi => lt_of_le_of_lt Nat.and_le_left (hf i hi)]
  split <;> simp

/-- Union of packed tables acts independently in every lane. -/
lemma packF_or (width size : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ width) :
    packF width size f ||| packF width size g =
      packF width size (fun i => f i ||| g i) := by
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_or, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hg,
    lane_packF _ _ _ _ fun i hi => Nat.or_lt_two_pow (hf i hi) (hg i hi)]
  split <;> simp

/-- Exclusive-or of packed tables acts independently in every lane. -/
lemma packF_xor (width size : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) (hg : ∀ i < size, g i < 2 ^ width) :
    packF width size f ^^^ packF width size g =
      packF width size (fun i => f i ^^^ g i) := by
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_xor, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hg,
    lane_packF _ _ _ _ fun i hi => Nat.xor_lt_two_pow (hf i hi) (hg i hi)]
  split <;> simp

/-- Algebraic addition of packed finite tables adds corresponding entries. -/
lemma packF_add (width size : Nat) (f g : Nat → Nat) :
    packF width size f + packF width size g = packF width size (fun i => f i + g i) := by
  unfold packF
  rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  simp only [List.zipWith_map, List.zipWith_self]

/-- Subtracting a pointwise smaller packed table subtracts in every lane. -/
lemma packF_sub (width size : Nat) (f g : Nat → Nat)
    (h : ∀ i < size, g i ≤ f i) :
    packF width size f - packF width size g = packF width size (fun i => f i - g i) := by
  have heq : packF width size (fun i => f i - g i) + packF width size g =
      packF width size f := by
    rw [packF_add]
    exact packF_congr _ _ _ _ fun i hi => Nat.sub_add_cancel (h i hi)
  omega

/-- Multiplication by a scalar multiplies every algebraically packed lane. -/
lemma packF_mul (width size scalar : Nat) (f : Nat → Nat) :
    scalar * packF width size f = packF width size (fun i => scalar * f i) := by
  simp only [packF, Nat.mul_ofDigits, List.map_map, Function.comp_def]

/-- Multiplying the packed all-ones table by a value packs the constant
table with that value. -/
lemma repeat_mul_eq_packF (width size value : Nat) :
    packF width size (fun _ => 1) * value = packF width size (fun _ => value) := by
  rw [Nat.mul_comm, packF_mul]
  simp only [Nat.mul_one]

/-- Packing commutes with a finite sum of lane tables. -/
lemma packF_list_sum (width size : Nat) (tables : List (Nat → Nat)) :
    (tables.map (packF width size)).sum =
      packF width size (fun i => (tables.map (fun f => f i)).sum) := by
  induction tables with
  | nil => simp [packF]
  | cons f fs ih => simp only [List.map_cons, List.sum_cons, ih, packF_add]

/-- Splitting a finite table splits its packed integer at the
corresponding lane. -/
lemma packF_split (width left right : Nat) (f : Nat → Nat) :
    packF width (left + right) f = packF width left f +
      2 ^ (width * left) * packF width right (fun i => f (left + i)) := by
  simp [packF, List.range_add, List.map_append, List.map_map,
    Nat.ofDigits_append, Nat.pow_mul, Function.comp_def]

/-- Appending one table entry appends its digit to the packed natural. -/
lemma packF_succ (width size : Nat) (f : Nat → Nat) :
    packF width (size + 1) f = packF width size f + 2 ^ (width * size) * f size := by
  rw [packF_split width size 1]
  simp [packF]

/-- Adding the two halves of a table adds the entries of the upper half to
those of the lower half. -/
lemma packF_merge (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    (packF width (size + size) f &&& (2 ^ (width * size) - 1)) +
      (packF width (size + size) f >>> (width * size)) =
      packF width size (fun i => f i + f (size + i)) := by
  rw [packF_split, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hb := packF_lt _ _ _ hw hf
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb, Nat.zero_add]
  exact packF_add _ _ _ _

/-- Concatenating two finite tables concatenates their packed lane blocks. -/
lemma packF_append (width left right : Nat) (f g : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < left, f i < 2 ^ width) (hg : ∀ i < right, g i < 2 ^ width) :
    packF width left f ||| (packF width right g <<< (width * left)) =
      packF width (left + right) (fun i => if i < left then f i else g (i - left)) := by
  have hh : ∀ i < left + right, (if i < left then f i else g (i - left)) < 2 ^ width := by
    intro i hi
    split
    · exact hf i (by assumption)
    · exact hg (i - left) (by omega)
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_or, lane_packF _ _ _ _ hf, lane_shiftLeft,
    lane_packF _ _ _ _ hg, lane_packF _ _ _ _ hh]
  by_cases hi : i < left
  · simp [hi, show ¬ left ≤ i by omega, show i < left + right by omega]
  · by_cases hir : i < left + right
    · simp [hi, show left ≤ i by omega, hir, show i - left < right by omega]
    · simp [hi, show left ≤ i by omega, hir, show ¬ i - left < right by omega]

/-- Concatenating a packed table with itself doubles it. -/
lemma packF_duplicate (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    packF width size f ||| (packF width size f <<< (width * size)) =
      packF width (size + size) (fun i => if i < size then f i else f (i - size)) :=
  packF_append width size size f f hw hf hf

/-! ## Lane selection -/

/-- An all-ones lane or a zero lane fits in the lane width. -/
private lemma mask_lt (width : Nat) (c : Prop) [Decidable c] :
    (if c then 2 ^ width - 1 else 0) < 2 ^ width := by
  have := Nat.two_pow_pos width
  split <;> omega

/-- A table entry or zero fits in the lane width if the entry does. -/
private lemma select_lt {width a : Nat} (c : Prop) [Decidable c] (h : a < 2 ^ width) :
    (if c then a else 0) < 2 ^ width := by
  split
  · exact h
  · exact Nat.two_pow_pos _

/-- A packed Boolean mask chooses whole lanes of a packed table. -/
lemma packF_mask (width size : Nat) (f : Nat → Nat) (p : Nat → Bool)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width) :
    packF width size f &&& packF width size (fun i => if p i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if p i then f i else 0) := by
  rw [packF_and _ _ _ _ hw hf fun i _ => mask_lt width _]
  refine packF_congr _ _ _ _ fun i hi => ?_
  cases p i <;> simp [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf i hi)]

/-- A repeated low-bit mask truncates every packed lane independently. -/
lemma packF_clip (width size keep : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hk : keep ≤ width) (hf : ∀ i < size, f i < 2 ^ width) :
    packF width size f &&& packF width size (fun _ => 2 ^ keep - 1) =
      packF width size (fun i => f i % 2 ^ keep) := by
  have hm : ∀ i < size, 2 ^ keep - 1 < 2 ^ width := fun _ _ =>
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      (Nat.pow_le_pow_right Nat.two_pos hk)
  rw [packF_and _ _ _ _ hw hf hm]
  exact packF_congr _ _ _ _ fun i _ => Nat.and_two_pow_sub_one_eq_mod _ _

/-- Exclusive-or of Boolean lane masks corresponds to exclusive-or of
selectors. -/
lemma packF_mask_xor (width size : Nat) (p q : Nat → Bool) (hw : 0 < width) :
    packF width size (fun i => if p i then 2 ^ width - 1 else 0) ^^^
      packF width size (fun i => if q i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if p i ^^ q i then 2 ^ width - 1 else 0) := by
  rw [packF_xor _ _ _ _ hw (fun i _ => mask_lt width _) (fun i _ => mask_lt width _)]
  refine packF_congr _ _ _ _ fun i _ => ?_
  cases p i <;> cases q i <;> simp

/-- Intersection of Boolean lane masks corresponds to conjunction of
selectors. -/
lemma packF_mask_and (width size : Nat) (p q : Nat → Bool) (hw : 0 < width) :
    packF width size (fun i => if p i then 2 ^ width - 1 else 0) &&&
      packF width size (fun i => if q i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if p i && q i then 2 ^ width - 1 else 0) := by
  rw [packF_and _ _ _ _ hw (fun i _ => mask_lt width _) (fun i _ => mask_lt width _)]
  refine packF_congr _ _ _ _ fun i _ => ?_
  cases p i <;> cases q i <;> simp

/-- Complementing a lane-selection mask complements the Boolean selector. -/
lemma packF_complement_mask (width size : Nat) (p : Nat → Bool) (hw : 0 < width) :
    packF width size (fun _ => 2 ^ width - 1) ^^^
      packF width size (fun i => if p i then 2 ^ width - 1 else 0) =
      packF width size (fun i => if !(p i) then 2 ^ width - 1 else 0) :=
  (packF_mask_xor width size (fun _ => true) p hw).trans
    (packF_congr _ _ _ _ fun i _ => by simp)

/-- A shorter all-ones prefix is a lane-selection mask in a larger table. -/
lemma prefixMask_eq_packF (width size count : Nat) (hw : 0 < width) (hp : count ≤ size) :
    2 ^ (width * count) - 1 =
      packF width size (fun i => if i < count then 2 ^ width - 1 else 0) := by
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_lowMask, lane_packF _ _ _ _ fun i _ => mask_lt width _]
  split_ifs <;> omega

/-- An all-ones prefix is the constant all-ones finite lane table. -/
lemma lowMask_eq_packF (width size : Nat) (hw : 0 < width) :
    2 ^ (width * size) - 1 = packF width size (fun _ => 2 ^ width - 1) :=
  (prefixMask_eq_packF width size size hw le_rfl).trans
    (packF_congr _ _ _ _ fun _ hi => if_pos hi)

/-- Multiplying the selected lanes of a table by `2 ^ shift`, truncated to the
lane width, is one masked shift: the unselected lanes are kept, and the
selected lanes are clipped to `keep` bits and shifted. -/
theorem packF_weight_step (width size keep shift : Nat) (f : Nat → Nat)
    (p : Nat → Bool) (hw : 0 < width) (hs : keep + shift = width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    (packF width size f &&& packF width size (fun i => if !(p i) then 2 ^ width - 1 else 0)) |||
      Nat.shiftLeft ((packF width size f &&&
        packF width size (fun i => if p i then 2 ^ width - 1 else 0)) &&&
        packF width size (fun _ => 2 ^ keep - 1)) shift =
    packF width size (fun i => if p i then Nat.shiftLeft (f i % 2 ^ keep) shift else f i) := by
  have hshift : ∀ i < size,
      Nat.shiftLeft ((if p i then f i else 0) % 2 ^ keep) shift < 2 ^ width := by
    intro i hi
    have h := Nat.shiftLeft_lt (m := shift)
      (Nat.mod_lt (if p i then f i else 0) (Nat.two_pow_pos keep))
    simpa [hs] using h
  rw [packF_mask _ _ _ _ hw hf, packF_mask _ _ _ _ hw hf,
    packF_clip _ _ _ _ hw (by omega) (fun i hi => select_lt _ (hf i hi)), packF_shiftLeft,
    packF_or _ _ _ _ hw (fun i hi => select_lt _ (hf i hi)) hshift]
  refine packF_congr _ _ _ _ fun i _ => ?_
  cases p i <;> simp

/-- Clipping to `keep` bits before shifting by `shift` is multiplication by
`2 ^ shift` modulo `2 ^ (keep + shift)`. -/
lemma clip_shift_eq_mod (value keep shift : Nat) :
    Nat.shiftLeft (value % 2 ^ keep) shift =
      (value * 2 ^ shift) % 2 ^ (keep + shift) := by
  change (value % 2 ^ keep) <<< shift = (value * 2 ^ shift) % 2 ^ (keep + shift)
  rw [Nat.shiftLeft_eq, pow_add]
  simpa [Nat.mul_comm] using (Nat.mul_mod_mul_left (2 ^ shift) value (2 ^ keep)).symm

/-! ## Packed lists -/

/-- A list of entries below `2 ^ width` packs into `width` bits per entry. -/
private lemma ofDigits_lt (width : Nat) (values : List Nat)
    (h : ∀ v ∈ values, v < 2 ^ width) :
    Nat.ofDigits (2 ^ width) values < 2 ^ (width * values.length) := by
  rcases Nat.eq_zero_or_pos width with rfl | hw
  · have hz : Nat.ofDigits 1 values = 0 := by
      rw [Nat.ofDigits_one]
      exact List.sum_eq_zero fun v hv => by simpa using h v hv
    simp [hz]
  · rw [Nat.pow_mul]
    exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow hw.ne') h

/-- Concatenating two lists concatenates their packed bit blocks. -/
lemma pack_append (width : Nat) (left right : List Nat)
    (hleft : ∀ v ∈ left, v < 2 ^ width) :
    Nat.ofDigits (2 ^ width) (left ++ right) =
      Nat.ofDigits (2 ^ width) left |||
        Nat.shiftLeft (Nat.ofDigits (2 ^ width) right) (width * left.length) := by
  rw [Nat.ofDigits_append, ← Nat.pow_mul, Nat.mul_comm _ (Nat.ofDigits _ right),
    ← Nat.shiftLeft_eq, Nat.add_comm,
    Nat.shiftLeft_add_eq_or_of_lt (ofDigits_lt width left hleft), Nat.or_comm]
  rfl

/-- For two packed lists of equal length, adding the low block and the high
block of their concatenation adds the lists entrywise. -/
lemma pack_merge_halves (width : Nat) (left right : List Nat)
    (hleft : ∀ v ∈ left, v < 2 ^ width) (hlen : left.length = right.length) :
    let packed := Nat.ofDigits (2 ^ width) (left ++ right)
    Nat.land packed (2 ^ (width * left.length) - 1) +
      Nat.shiftRight packed (width * left.length) =
      Nat.ofDigits (2 ^ width) (left.zipWith (· + ·) right) := by
  dsimp
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.ofDigits_append, ← Nat.pow_mul]
  have hb := ofDigits_lt width left hleft
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb, Nat.zero_add]
  exact Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq hlen

/-! ## Repeated blocks -/

/-- `value` followed by a second copy of itself `width` bits higher. -/
def doubleBlock (value width : Nat) : Nat := value ||| value <<< width

/-- A doubled block occupies precisely twice the original bit capacity. -/
lemma doubleBlock_lt (value width : Nat) (h : value < 2 ^ width) :
    doubleBlock value width < 2 ^ (2 * width) := by
  simpa [doubleBlock, Nat.two_mul, Nat.or_comm] using Nat.append_lt h h

/-- Bit `j` of a doubled block is bit `j % width` of the block, for `j` below
`2 * width`. -/
lemma testBit_doubleBlock (value width j : Nat) (h : value < 2 ^ width) :
    (doubleBlock value width).testBit j =
      (decide (j < 2 * width) && value.testBit (j % width)) := by
  by_cases hj : j < width
  · simp [doubleBlock, Nat.testBit_shiftLeft, Nat.mod_eq_of_lt hj,
      show ¬ width ≤ j by omega, show j < 2 * width by omega]
  · have hjw : width ≤ j := by omega
    have hvj := testBit_eq_false_of_lt h hjw
    by_cases hj2 : j < 2 * width
    · have hm : j % width = j - width := by
        rw [Nat.mod_eq_sub_mod hjw, Nat.mod_eq_of_lt (by omega)]
      simp [doubleBlock, Nat.testBit_shiftLeft, hvj, hjw, hj2, hm]
    · have hvjw := testBit_eq_false_of_lt h (show width ≤ j - width by omega)
      simp [doubleBlock, Nat.testBit_shiftLeft, hvj, hjw, hj2, hvjw]

/-- `2 ^ e` consecutive copies of a block of `width` bits, built by `e`
successive doublings. -/
def repeatBlock : Nat → Nat → Nat → Nat
  | value, _, 0 => value
  | value, width, e + 1 => repeatBlock (doubleBlock value width) (2 * width) e

/-- Bit `j` of a repeated block is bit `j % width` of the block, for `j` below
`width * 2 ^ e`. -/
lemma testBit_repeatBlock (value width e j : Nat) (hw : 0 < width)
    (hv : value < 2 ^ width) :
    (repeatBlock value width e).testBit j =
      (decide (j < width * 2 ^ e) && value.testBit (j % width)) := by
  induction e generalizing value width with
  | zero =>
    simp only [repeatBlock, pow_zero, Nat.mul_one]
    by_cases hj : j < width
    · simp [hj, Nat.mod_eq_of_lt hj]
    · simp [hj, testBit_eq_false_of_lt hv (show width ≤ j by omega)]
  | succ e ih =>
    rw [repeatBlock, ih _ _ (by omega) (doubleBlock_lt _ _ hv),
      testBit_doubleBlock _ _ _ hv]
    have hm : (j % (2 * width)) % width = j % width :=
      Nat.mod_mod_of_dvd j (by simp)
    simp only [Nat.mod_lt _ (by omega : 0 < 2 * width), decide_true, Bool.true_and, hm]
    simp [pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- Repeating a block of `size` lanes repeats those lanes periodically. -/
lemma lane_repeatBlock_wide (value width size e i : Nat) (hw : 0 < width)
    (hs : 0 < size) (hv : value < 2 ^ (width * size)) :
    lane width i (repeatBlock value (width * size) e) =
      if i < size * 2 ^ e then lane width (i % size) value else 0 := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_lane, testBit_repeatBlock _ _ _ _ (Nat.mul_pos hw hs) hv]
  by_cases hj : j < width
  · rw [mul_add_mod_mul _ _ _ _ hj, Nat.mul_assoc]
    simp only [mul_add_lt_mul_iff hj]
    split <;> simp_all [testBit_lane]
  · split <;> simp [hj, testBit_lane]

/-- Every lane of a repeated block is the original block. -/
lemma lane_repeatBlock (value width e i : Nat) (hw : 0 < width)
    (hv : value < 2 ^ width) :
    lane width i (repeatBlock value width e) = if i < 2 ^ e then value else 0 := by
  have h := lane_repeatBlock_wide value width 1 e i hw Nat.one_pos (by simpa using hv)
  simpa [Nat.mod_one, lane_eq_div_mod, Nat.mod_eq_of_lt hv] using h

/-- A repeated block is the packed constant table. -/
theorem repeatBlock_eq_packF (value width e : Nat) (hw : 0 < width)
    (hv : value < 2 ^ width) :
    repeatBlock value width e = packF width (2 ^ e) (fun _ => value) := by
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_repeatBlock _ _ _ _ hw hv, lane_packF _ _ _ _ (fun _ _ => hv)]

/-- Repeating an all-ones block yields an all-ones block of the combined
width. -/
lemma repeatBlock_lowMask (width e : Nat) (hw : 0 < width) :
    repeatBlock (2 ^ width - 1) width e = 2 ^ (width * 2 ^ e) - 1 := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_repeatBlock _ _ _ _ hw (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)]
  simp [Nat.mod_lt _ hw]

/-! ## Masks selecting a binary digit of the lane index -/

/-- Bit `p` of `i` is clear exactly when `i` lies in the lower half of its
residue class modulo `2 ^ (p + 1)`. -/
lemma not_testBit_eq_decide_mod_lt (i p : Nat) :
    (!(i.testBit p)) = decide (i % 2 ^ (p + 1) < 2 ^ p) := by
  have hdiv : i % 2 ^ (p + 1) / 2 ^ p = i / 2 ^ p % 2 := by
    rw [pow_succ, Nat.mod_mul_right_div_self]
  have heq : i % 2 ^ (p + 1) < 2 ^ p ↔ i / 2 ^ p % 2 = 0 := by
    rw [← hdiv, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  simp only [Nat.testBit_eq_decide_div_mod_eq, heq]
  rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ p) with h | h <;> simp [h]

/-- The top bit of a number below `2 ^ (bits + 1)` is set exactly when the
number is at least `2 ^ bits`. -/
lemma testBit_eq_decide_le {bits x : Nat} (hx : x < 2 ^ (bits + 1)) :
    x.testBit bits = decide (2 ^ bits ≤ x) := by
  have h := not_testBit_eq_decide_mod_lt x bits
  rw [Nat.mod_eq_of_lt hx] at h
  rw [← Bool.not_not (x.testBit bits), h, ← decide_not]
  exact decide_eq_decide.mpr Nat.not_lt

/-- The mask selecting, in a table of `2 ^ bits` lanes of `width` bits, the
lanes whose index has bit `position` clear, built as a periodic block. -/
def bitZeroMask (width bits position : Nat) : Nat :=
  repeatBlock (2 ^ (width * 2 ^ position) - 1) (width * 2 ^ (position + 1))
    (bits - position - 1)

/-- `bitZeroMask` is the lane-selection mask of the lanes whose index has bit
`position` clear. -/
theorem bitZeroMask_eq_packF (width bits position : Nat) (hw : 0 < width)
    (hp : position < bits) :
    bitZeroMask width bits position =
      packF width (2 ^ bits) (fun i => if !(i.testBit position) then 2 ^ width - 1 else 0) := by
  have hv : 2 ^ (width * 2 ^ position) - 1 < 2 ^ (width * 2 ^ (position + 1)) :=
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      (Nat.pow_le_pow_right Nat.two_pos
        (Nat.mul_le_mul_left width (Nat.pow_le_pow_right Nat.two_pos (Nat.le_succ _))))
  have hsize : 2 ^ (position + 1) * 2 ^ (bits - position - 1) = 2 ^ bits := by
    rw [← pow_add]
    congr 1
    omega
  refine eq_of_lane_eq hw fun i => ?_
  rw [bitZeroMask, lane_repeatBlock_wide _ _ _ _ _ hw (Nat.two_pow_pos _) hv,
    hsize, lane_lowMask,
    lane_packF _ _ _ _ fun i _ => mask_lt width _,
    not_testBit_eq_decide_mod_lt]
  split <;> simp_all

/-- Folding `bitZeroMask`s into a lane-selection mask by XOR folds the
corresponding index bits into its selector. -/
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
    rw [List.foldl_cons, bitZeroMask_eq_packF _ _ _ hw (hp p List.mem_cons_self),
      packF_mask_xor _ _ _ _ hw, ih _ fun q hq => hp q (List.mem_cons_of_mem p hq)]
    rfl

/-! ## Lane transport -/

/-- The value arriving in lane `i` when the lanes outside `up` and `down` stay
in place, the `up` lanes move up by `delta` and the `down` lanes move down by
`delta`. -/
def transportedValue (size delta i : Nat) (f : Nat → Nat) (up down : Nat → Bool) : Nat :=
  (if !(up i ^^ down i) then f i else 0) |||
    (if delta ≤ i then
      if i - delta < size then if up (i - delta) then f (i - delta) else 0 else 0 else 0) |||
    (if i + delta < size then if down (i + delta) then f (i + delta) else 0 else 0)

/-- Keeping the lanes outside `up` and `down`, shifting the `up` lanes up by
`delta` and the `down` lanes down by `delta` realizes the lane permutation
`source`, provided each lane's transported value is the entry at its source. -/
theorem packF_transport (width size delta : Nat) (f source : Nat → Nat)
    (up down : Nat → Bool) (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width)
    (hsource : ∀ i < size, source i < size)
    (hup : ∀ i < size, up i = true → i + delta < size)
    (hmove : ∀ i < size, transportedValue size delta i f up down = f (source i)) :
    packF width size (fun i => if !(up i ^^ down i) then f i else 0) |||
      (packF width size (fun i => if up i then f i else 0) <<< (width * delta)) |||
      (packF width size (fun i => if down i then f i else 0) >>> (width * delta)) =
      packF width size (fun i => f (source i)) := by
  have hsel (p : Nat → Bool) : ∀ i < size, (if p i then f i else 0) < 2 ^ width :=
    fun i hi => select_lt _ (hf i hi)
  refine eq_of_lane_eq hw fun i => ?_
  rw [lane_or, lane_or, lane_shiftLeft, lane_shiftRight,
    lane_packF _ _ _ _ (hsel (fun i => !(up i ^^ down i))),
    lane_packF _ _ _ _ (hsel up), lane_packF _ _ _ _ (hsel down),
    lane_packF _ _ _ _ (fun i hi => hf _ (hsource i hi))]
  by_cases hi : i < size
  · simpa [hi, transportedValue] using hmove i hi
  · have hlow : (if delta ≤ i then
        if i - delta < size then
          if up (i - delta) then f (i - delta) else 0 else 0 else 0) = 0 := by
      split_ifs with hd hr hu
      · have := hup (i - delta) hr hu
        omega
      all_goals rfl
    simp [hi, show ¬ i + delta < size by omega, hlow]

/-- The scalar check for lane `i` of a transport: `source i` is in range, an
upward-moving lane `i` stays inside the table, and exactly one of the three
contributions (staying, from below, from above) arrives in lane `i`, from lane
`source i`. -/
def checkTransport (size delta i : Nat) (up down : Nat → Bool) (source : Nat → Nat) : Bool :=
  let stay := !(up i ^^ down i)
  let fromLow := decide (delta ≤ i) && decide (i - delta < size) && up (i - delta)
  let fromHigh := decide (i + delta < size) && down (i + delta)
  decide (source i < size) && (!(up i) || decide (i + delta < size)) &&
    ((stay && !fromLow && !fromHigh && decide (source i = i)) ||
     (!stay && fromLow && !fromHigh && decide (source i = i - delta)) ||
     (!stay && !fromLow && fromHigh && decide (source i = i + delta)))

/-- A passing transport check bounds the source index. -/
lemma checkTransport_source {size delta i : Nat} {up down : Nat → Bool} {source : Nat → Nat}
    (h : checkTransport size delta i up down source = true) : source i < size := by
  simp only [checkTransport, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- A passing transport check keeps an upward-moving lane within the table. -/
lemma checkTransport_up {size delta i : Nat} {up down : Nat → Bool} {source : Nat → Nat}
    (h : checkTransport size delta i up down source = true) (hu : up i = true) :
    i + delta < size := by
  have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  simpa [hu] using hh

/-- If exactly one of three selectors is set and `source` is the matching
index, the three selected values combine to `f source`. -/
lemma transportValues_of_certificate (stay low high : Bool) (source i delta : Nat)
    (f : Nat → Nat)
    (h : ((stay && !low && !high && decide (source = i)) ||
      (!stay && low && !high && decide (source = i - delta)) ||
      (!stay && !low && high && decide (source = i + delta))) = true) :
    (if stay then f i else 0) ||| (if low then f (i - delta) else 0) |||
      (if high then f (i + delta) else 0) = f source := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h <;> simp_all

/-- A passing transport check identifies the value arriving in the lane,
whatever the table contents. -/
lemma checkTransport_value {size delta i : Nat} {up down : Nat → Bool} {source : Nat → Nat}
    (h : checkTransport size delta i up down source = true) (f : Nat → Nat) :
    transportedValue size delta i f up down = f (source i) := by
  have ht := transportValues_of_certificate (!(up i ^^ down i))
    (decide (delta ≤ i) && decide (i - delta < size) && up (i - delta))
    (decide (i + delta < size) && down (i + delta)) (source i) i delta f
    (Bool.and_eq_true_iff.mp h).2
  simpa [transportedValue, Bool.and_eq_true, ite_and] using ht

/-- If `checkTransport` passes in every lane, the three masked operations —
keep the lanes outside `up` and `down`, shift the `up` lanes up and the `down`
lanes down by `delta` — permute the table by `source`. -/
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

/-! ## Bounded packed polynomials -/

/-- `value` packs `degree + 1` coefficients, each at most `bound`, into slots
of `slot` bits. -/
def BoundedPolynomial (slot degree bound value : Nat) : Prop :=
  ∃ coefficients : List Nat, coefficients.length = degree + 1 ∧
    (∀ c ∈ coefficients, c ≤ bound) ∧ Nat.ofDigits (2 ^ slot) coefficients = value

/-- A bounded polynomial fits in its allocated lane whenever its
coefficients fit their slots. -/
lemma BoundedPolynomial.lt {slot degree bound value : Nat}
    (h : BoundedPolynomial slot degree bound value) (hs : 0 < slot) (hb : bound < 2 ^ slot) :
    value < 2 ^ (slot * (degree + 1)) := by
  obtain ⟨coefficients, hlen, hbound, rfl⟩ := h
  rw [Nat.pow_mul, ← hlen]
  exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow hs.ne')
    (fun c hc => lt_of_le_of_lt (hbound c hc) hb)

/-- The zero polynomial satisfies every coefficient bound. -/
lemma BoundedPolynomial.zero (slot degree bound : Nat) :
    BoundedPolynomial slot degree bound 0 := by
  refine ⟨List.replicate (degree + 1) 0, by simp, fun c hc => ?_, by simp⟩
  simp only [List.mem_replicate] at hc
  omega

/-- The constant polynomial `1` has coefficients at most one. -/
lemma BoundedPolynomial.one (slot degree : Nat) :
    BoundedPolynomial slot degree 1 1 := by
  refine ⟨1 :: List.replicate degree 0, by simp, fun c hc => ?_, by simp [Nat.ofDigits_cons]⟩
  simp only [List.mem_cons, List.mem_replicate] at hc
  omega

/-- Increasing a coefficient bound preserves the bounded-polynomial
predicate. -/
lemma BoundedPolynomial.mono {slot degree bound bound' value : Nat}
    (h : BoundedPolynomial slot degree bound value) (hb : bound ≤ bound') :
    BoundedPolynomial slot degree bound' value := by
  obtain ⟨coefficients, hlen, hbound, hvalue⟩ := h
  exact ⟨coefficients, hlen, fun c hc => (hbound c hc).trans hb, hvalue⟩

/-- Adding packed polynomials adds their coefficient bounds; no bound on the
carries is needed. -/
theorem BoundedPolynomial.add {slot degree bound bound' value value' : Nat}
    (h : BoundedPolynomial slot degree bound value)
    (h' : BoundedPolynomial slot degree bound' value') :
    BoundedPolynomial slot degree (bound + bound') (value + value') := by
  obtain ⟨a, ha, hca, rfl⟩ := h
  obtain ⟨b, hb, hcb, rfl⟩ := h'
  refine ⟨a.zipWith (· + ·) b, by simp [ha, hb], fun c hc => ?_,
    (Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (ha.trans hb.symm)).symm⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  simp only [List.getElem_zipWith]
  exact Nat.add_le_add (hca _ (List.getElem_mem ..)) (hcb _ (List.getElem_mem ..))

/-- Multiplying a polynomial by the variable and truncating to the same degree
preserves its coefficient bound. -/
theorem BoundedPolynomial.shift {slot degree bound value : Nat}
    (h : BoundedPolynomial slot degree bound value) (hb : bound < 2 ^ slot) :
    BoundedPolynomial slot degree bound ((value * 2 ^ slot) % 2 ^ (slot * (degree + 1))) := by
  obtain ⟨coefficients, hlen, hbound, rfl⟩ := h
  have hcoeff : ∀ c ∈ 0 :: coefficients, c < 2 ^ slot := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.two_pow_pos _
    · exact lt_of_le_of_lt (hbound c hc) hb
  refine ⟨(0 :: coefficients).take (degree + 1), by simp [hlen], fun c hc => ?_, ?_⟩
  · rcases List.mem_cons.mp (List.mem_of_mem_take hc) with rfl | hc
    · omega
    · exact hbound c hc
  · rw [Nat.pow_mul, ← Nat.ofDigits_mod_pow_eq_ofDigits_take (degree + 1)
      (Nat.two_pow_pos slot) (0 :: coefficients) hcoeff]
    simp [Nat.ofDigits_cons, Nat.mul_comm]

end PackedDigits

import QEC.Stabilizer.Framework.Homological.Certificate.OrbitPackedExtra

namespace PackedDigits

/-- Spread the low `count` bits of a natural number into separate fixed-width lanes. -/
def dilate (width count value : Nat) : Nat :=
  packF width count (fun i => if value.testBit i then 1 else 0)

/-- Each spread bit fits in every positive lane width. -/
theorem bit_value_lt (width value i : Nat) (hw : 0 < width) :
    (if value.testBit i then 1 else 0) < 2^width := by
  have h := Nat.one_lt_two_pow hw.ne'
  split <;> omega

/-- Spreading adjacent input blocks concatenates their output blocks. -/
theorem dilate_append (width left right value : Nat) (hw : 0 < width) :
    dilate width (left+right) value =
      dilate width left (value % 2^left) |||
        (dilate width right (value >>> left) <<< (width*left)) := by
  unfold dilate
  rw [packF_append _ _ _ _ _ hw
    (fun i _ => bit_value_lt _ _ _ hw) (fun i _ => bit_value_lt _ _ _ hw)]
  apply packF_congr
  intro i hi
  by_cases h : i < left
  · simp [h, Nat.testBit_mod_two_pow]
  · simp [h, Nat.testBit_shiftRight, Nat.add_sub_cancel' (by omega : left ≤ i)]

/-- A small lookup table can implement one block of a bit spread. -/
def dilationLookup (stride table x : Nat) : Nat :=
  Nat.land (Nat.shiftRight table (Nat.mul stride x)) (2^stride-1)

/-- Evaluate a uniform bit spread using a repeated small lookup table. -/
def fastDilation (width chunk table : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | count+1, value =>
    Nat.lor (dilationLookup (width*chunk) table (value % 2^chunk))
      (Nat.shiftLeft (fastDilation width chunk table count (value >>> chunk)) (width*chunk))

/-- One certified lookup table makes every repeated block spread exact. -/
theorem fastDilation_eq (width chunk table : Nat) (hw : 0 < width)
    (hlookup : ∀ x : Fin (2^chunk), dilationLookup (width*chunk) table x = dilate width chunk x) :
    ∀ count value, fastDilation width chunk table count value = dilate width (chunk*count) value := by
  intro count
  induction count with
  | zero => intro value; simp [fastDilation, dilate, packF]
  | succ count ih =>
    intro value
    rw [fastDilation, hlookup ⟨value % 2^chunk, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, ih]
    rw [Nat.mul_succ, Nat.add_comm (chunk*count) chunk, dilate_append _ _ _ _ hw]
    rfl

/-- Spreading and filling a selected lane makes every bit of that row constant. -/
theorem dilate_fill (width count fill value : Nat) :
    dilate width count value * fill =
      packF width count (fun i => if value.testBit i then fill else 0) := by
  rw [Nat.mul_comm, dilate, packF_mul]
  apply packF_congr
  intro i hi
  cases value.testBit i <;> simp

/-- Repeating a word is multiplication by a packed table of ones. -/
theorem repeat_word (width count value : Nat) :
    value * packF width count (fun _ => 1) = packF width count (fun _ => value) := by
  rw [packF_mul]
  simp

/-- The XOR of a filled spread and a repeated word is the pairwise-XOR bit plane. -/
theorem pairPlane_bit (width count value q r : Nat) (hw : 0 < width)
    (hc : count < width) (hv : value < 2^count) (hq : q < count) (hr : r < count) :
    ((dilate width count value * (2^count-1)) ^^^
      (value * packF width count (fun _ => 1))).testBit (width*q+r) =
      (value.testBit q ^^ value.testBit r) := by
  rw [dilate_fill, repeat_word, Nat.testBit_xor]
  have hm : ∀ i < count, (if value.testBit i then 2^count-1 else 0) < 2^width := by
    intro i hi
    have hp := Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hc
    have hp' := Nat.two_pow_pos count
    split <;> omega
  have hvw : ∀ i < count, value < 2^width := fun _ _ => lt_trans hv
    (Nat.pow_lt_pow_right (by decide) hc)
  rw [testBit_packF_at _ _ _ _ _ hm (by omega), if_pos hq,
    testBit_packF_at _ _ _ _ _ hvw (by omega), if_pos hq]
  cases value.testBit q <;> simp [hr]

#print axioms fastDilation_eq
#print axioms pairPlane_bit
end PackedDigits

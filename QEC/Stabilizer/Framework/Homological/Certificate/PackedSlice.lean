import QEC.Stabilizer.Framework.Homological.Certificate.AffineBatchBoundary

namespace PackedDigits
/-- A bounded consecutive block of lanes. -/
def boundedSlice (width start size value : Nat) : Nat :=
  (value >>> (width*start)) &&& (2^(width*size)-1)

/-- Reading an extracted lane is reading the corresponding original lane. -/
theorem lane_boundedSlice (width start size value i : Nat) (hw : 0 < width) (hi : i < size) :
    lane width i (boundedSlice width start size value) = lane width (i+start) value := by
  rw [boundedSlice, lane_and, lane_lowMask _ _ _ hw, if_pos hi,
    Nat.and_two_pow_sub_one_of_lt_two_pow (lane_lt _ _ _), lane_shiftRight]

/-- A lane-wise relation restricts to every bounded consecutive slice of its tables. -/
theorem predicate_of_slice (R : Nat → Nat → Prop)
    (width total start size tableA tableB localA localB : Nat)
    (hw : 0 < width) (hsize : start+size ≤ total)
    (hglobal : ∀ i < total, R (lane width i tableA) (lane width i tableB))
    (ha : localA = boundedSlice width start size tableA)
    (hb : localB = boundedSlice width start size tableB)
    (i : Nat) (hi : i < size) : R (lane width i localA) (lane width i localB) := by
  rw [ha, hb, lane_boundedSlice _ _ _ _ _ hw hi, lane_boundedSlice _ _ _ _ _ hw hi]
  exact hglobal _ (by omega)
end PackedDigits

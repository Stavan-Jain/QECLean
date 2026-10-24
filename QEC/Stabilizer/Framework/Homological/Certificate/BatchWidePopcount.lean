import QEC.Stabilizer.Framework.Homological.Certificate.PackedPopcount
import QEC.Stabilizer.Framework.Homological.Certificate.BatchDualRaw

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- Merge adjacent128-bit counts to obtain256-bit lane counts. -/
def popcount256 (r value : Nat) : Nat :=
  let prior := popcount128 (r * (1+2^128)) value
  let mask := r * (2^128-1)
  (prior &&& mask) + ((prior >>> 128) &&& mask)

/-- Merge adjacent256-bit counts to obtain512-bit lane counts. -/
def popcount512 (r value : Nat) : Nat :=
  let prior := popcount256 (r * (1+2^256)) value
  let mask := r * (2^256-1)
  (prior &&& mask) + ((prior >>> 256) &&& mask)

/-- Repeating two adjacent one digits changes the lane width without changing the mask. -/
theorem repeat_double (width size : Nat) :
    packF (2*width) size (fun _ => 1) * (1+2^width) =
      packF width (2*size) (fun _ => 1) := by
  rw [repeat_mul_eq_packF,packF_constant_group]
  have he : packF width 2 (fun _ => 1) = 1+2^width := by
    simp [packF,Nat.ofDigits]
  rw [he]
  congr 1
  omega

/-- The executable256-bit count is the proved eight-stage counting tree. -/
theorem popcount256_eq_tree (size value : Nat) :
    popcount256 (packF 256 size (fun _ => 1)) value = popcountTree 8 size value := by
  unfold popcount256
  rw [show (256:Nat)=2*128 by decide,repeat_double,popcount128_eq_tree]
  rw [repeat_mul_eq_packF]
  rfl

/-- The executable512-bit count is the proved nine-stage counting tree. -/
theorem popcount512_eq_tree (size value : Nat) :
    popcount512 (packF 512 size (fun _ => 1)) value = popcountTree 9 size value := by
  unfold popcount512
  rw [show (512:Nat)=2*256 by decide,repeat_double,popcount256_eq_tree]
  rw [repeat_mul_eq_packF]
  rfl

/-- Reading a lane of the proved counting tree gives its bounded mask's weight. -/
theorem popcountTree_lane (e size bits value : Nat) (hbits : bits ≤ 2^e)
    (hv : value < 2^(2^e*size))
    (hmask : value &&& (packF (2^e) size (fun _ => 1) * (2^bits-1)) = value)
    (i : Nat) (hi : i < size) :
    lane (2^e) i (popcountTree e size value) = bitCount bits (lane (2^e) i value) := by
  have hbound := lane_bound_of_parallel_mask (2^e) size bits value (Nat.two_pow_pos _) hbits hmask
  rw [popcountTree_eq e size value hv,lane_packF _ _ _ _ (fun j hj =>
    lt_of_le_of_lt (bitCount_le _ _) Nat.lt_two_pow_self),if_pos hi]
  rw [← bitCount_mod]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [← lane_eq_div_mod]
  have he := bitCount_extend bits (2^e-bits) (lane (2^e) i value) (hbound i hi)
  simpa [Nat.add_sub_of_le hbits] using he

/-- A parallel weight certificate yields each256-bit record's exact short-mask weight. -/
theorem popcount256_weight (size bits value expected : Nat) (hbits : bits ≤ 256)
    (hv : value < 2^(256*size))
    (hmask : value &&& (packF 256 size (fun _ => 1) * (2^bits-1)) = value)
    (hc : popcount256 (packF 256 size (fun _ => 1)) value =
      packF 256 size (fun _ => expected)) (he : expected < 2^256)
    (i : Nat) (hi : i < size) : bitCount bits (lane 256 i value) = expected := by
  have h := popcountTree_lane 8 size bits value hbits hv hmask i hi
  norm_num only [Nat.reducePow] at h
  rw [← popcount256_eq_tree,hc,lane_packF _ _ _ _ (fun _ _ => he),if_pos hi] at h
  exact h.symm

/-- A parallel weight certificate yields each512-bit record's exact short-mask weight. -/
theorem popcount512_weight (size bits value expected : Nat) (hbits : bits ≤ 512)
    (hv : value < 2^(512*size))
    (hmask : value &&& (packF 512 size (fun _ => 1) * (2^bits-1)) = value)
    (hc : popcount512 (packF 512 size (fun _ => 1)) value =
      packF 512 size (fun _ => expected)) (he : expected < 2^512)
    (i : Nat) (hi : i < size) : bitCount bits (lane 512 i value) = expected := by
  have h := popcountTree_lane 9 size bits value hbits hv hmask i hi
  norm_num only [Nat.reducePow] at h
  rw [← popcount512_eq_tree,hc,lane_packF _ _ _ _ (fun _ _ => he),if_pos hi] at h
  exact h.symm

#print axioms popcount256_weight
end PackedDigits

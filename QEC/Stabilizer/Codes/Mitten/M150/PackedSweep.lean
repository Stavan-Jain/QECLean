import QEC.Stabilizer.Codes.Mitten.M150.FloorCore
import QEC.Stabilizer.Framework.Homological.Certificate.PackedPopcount32
import QEC.Stabilizer.Framework.Homological.Certificate.PackedEquality
import QEC.Stabilizer.Framework.Homological.Certificate.PackedListCertificate

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask

/-- One flag in each 32-bit lane whose word has the specified weight. -/
def weightFlags (rep words weight : Nat) : Nat :=
  Nat.shiftRight
    (Nat.xor (Nat.mul rep 32)
      (Nat.land
        (Nat.add (Nat.xor (popcount32 rep words) (Nat.mul rep weight))
          (Nat.mul rep 31))
        (Nat.mul rep 32))) 5

/-- The packed arithmetic checks the popcount independently in each lane. -/
theorem weightFlags_spec (size weight : Nat) (f : Nat → Nat)
    (hf : ∀ i < size, f i < 2 ^ 30) (hw : weight < 32) :
    weightFlags (packF 32 size (fun _ => 1)) (packF 32 size f) weight =
      packF 32 size (fun i => if bitCount 30 (f i) = weight then 1 else 0) := by
  unfold weightFlags
  rw [popcount32_packF size f hf]
  change ((packF 32 size (fun _ => 1) * 32 ^^^
    (((packF 32 size (fun i => bitCount 30 (f i)) ^^^
      packF 32 size (fun _ => 1) * weight) +
      packF 32 size (fun _ => 1) * 31) &&&
      (packF 32 size (fun _ => 1) * 32))) >>> 5) = _
  simp only [repeat_mul_eq_packF]
  apply packed_equality_flags 32 size 5
  · decide
  · intro i _
    have := bitCount_le 30 (f i)
    omega
  · intro i _
    exact hw

/-- Sparse indices encoded as one flag in each selected lane. -/
def indexFlags : List Nat → Nat
  | [] => 0
  | i :: rest => Nat.lor (2 ^ (32 * i)) (indexFlags rest)

/-- A selected lane in the sparse certificate has a listed index. -/
theorem indexFlags_sound (xs : List Nat) (i : Nat)
    (h : (indexFlags xs).testBit (32 * i) = true) : i ∈ xs := by
  induction xs with
  | nil => simp [indexFlags] at h
  | cons j js ih =>
    change ((2 ^ (32 * j) ||| indexFlags js).testBit (32 * i)) = true at h
    simp only [Nat.testBit_or, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with he | ht
    · have : j = i := by omega
      simp [this]
    · exact List.mem_cons_of_mem _ (ih ht)

/-- Every word whose weight passes the batch check has a certified index. -/
theorem weightFlags_sound (size weight words : Nat) (f : Nat → Nat)
    (hf : ∀ i < size, f i < 2 ^ 30) (hw : weight < 32)
    (hwords : words = packF 32 size f) (exceptions : List Nat)
    (hcheck : weightFlags (packF 32 size (fun _ => 1)) words weight =
      indexFlags exceptions) (i : Nat) (hi : i < size)
    (hweight : bitCount 30 (f i) = weight) : i ∈ exceptions := by
  apply indexFlags_sound exceptions i
  rw [← hcheck, hwords, weightFlags_spec size weight f hf hw]
  have he := lane_packF 32 size i (fun j => if bitCount 30 (f j) = weight then 1 else 0)
    (by intro j _; dsimp only; split <;> decide)
  dsimp only at he
  rw [if_pos hi, if_pos hweight] at he
  have hb := congrArg (fun n : Nat => n.testBit 0) he
  simpa [lane, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] using hb

/-- A packed list and parallel linear map specify every image lane. -/
theorem packedImages_spec (xs : List Nat) (input rep : Nat)
    (columns : List (Nat × Nat)) (f : Nat → Nat)
    (hxs : ∀ x ∈ xs, x < 2 ^ 30)
    (hinput : input = packList 32 xs)
    (hrep : rep = packF 32 xs.length (fun _ => 1))
    (hcols : ∀ p ∈ columns, p.1 < 32 ∧ p.2 < 2 ^ 32)
    (hf : ∀ x < 2 ^ 30, reconX columns x = f x) :
    batchRecon rep input columns = packF 32 xs.length (fun i => f (xs.getD i 0)) := by
  rw [hrep, hinput, packList_eq_packF, batchRecon_packF _ _ _ (by decide)]
  · apply packF_congr
    intro i hi
    apply hf
    rw [List.getD_eq_getElem _ _ hi]
    exact hxs _ (List.getElem_mem hi)
  · intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact lt_of_lt_of_le (hxs _ (List.getElem_mem hi)) (by decide : 2 ^ 30 ≤ 2 ^ 32)
  · exact hcols

/-- The unit marker for every lane of a concrete mask block. -/
def packedOnes (xs : List Nat) : Nat := packList 32 (xs.map fun _ => 1)

/-- The concrete unit markers agree with the functional lane specification. -/
theorem packedOnes_eq (xs : List Nat) :
    packedOnes xs = packF 32 xs.length (fun _ => 1) := by
  unfold packedOnes
  rw [packList_eq_ofDigits]
  unfold packF
  congr 1
  simp

/-- Apply a certified binary map to all masks in a block simultaneously. -/
def packedImages (xs : List Nat) (columns : List (Nat × Nat)) : Nat :=
  forceNat (packedOnes xs) fun rep =>
  forceNat (packList 32 xs) fun input =>
    batchRecon rep input columns

/-- The concrete packed images represent the corresponding linear map. -/
theorem packedImages_eq (xs : List Nat) (columns : List (Nat × Nat)) (f : Nat → Nat)
    (hxs : ∀ x ∈ xs, x < 2 ^ 30)
    (hcols : ∀ p ∈ columns, p.1 < 32 ∧ p.2 < 2 ^ 32)
    (hf : ∀ x < 2 ^ 30, reconX columns x = f x) :
    packedImages xs columns = packF 32 xs.length (fun i => f (xs.getD i 0)) := by
  simpa only [packedImages, forceNat_eq] using
    packedImages_spec xs (packList 32 xs) (packedOnes xs) columns f
      hxs rfl (packedOnes_eq xs) hcols hf

end Quantum.Stabilizer.Homological.LP.M150

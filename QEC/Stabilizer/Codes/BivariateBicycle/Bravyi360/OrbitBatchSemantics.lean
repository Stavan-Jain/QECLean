import QEC.Stabilizer.Framework.Homological.Certificate.PackedLaneShifts
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.GBOrbitAction

noncomputable section

namespace Quantum.Stabilizer.Homological.GBOrbit.Batch
open PackedDigits

/-- The low two positions in every three-bit cell of a90-bit chain. -/
noncomputable def lowY : Nat := 0x1b6db6db6db6db6db6db6db
/-- The shifted high position in every three-bit cell of a90-bit chain. -/
noncomputable def highY : Nat := 0x9249249249249249249249
/-- The low windows remaining after an x-coordinate rotation. -/
noncomputable def lowX (x : Nat) : Nat := (2^(45-3*x)-1)*(1+2^45)
/-- The high windows filled by wraparound in an x-coordinate rotation. -/
noncomputable def highX (x : Nat) : Nat := ((2^(3*x)-1) <<< (45-3*x))*(1+2^45)

/-- Rotate y in every three-bit cell of one chain. -/
noncomputable def yword (v : Nat) : Nat := ((v &&& lowY) <<< 1) ||| ((v >>> 2) &&& highY)
/-- Rotate x independently in the two45-bit blocks of one chain. -/
noncomputable def xword (v x : Nat) : Nat :=
  ((v >>> (3*x)) &&& lowX x) ||| ((v <<< (45-3*x)) &&& highX x)

/-- Finite mask facts identify the unique source position of a y-rotation output bit. -/
theorem y_mask_certificate : ∀ j : Fin 90,
    if lowY.testBit (j.val-1) && decide (1 ≤ j.val) then
      highY.testBit j.val = false ∧ translateIndex 0 1 j.val = j.val-1
    else highY.testBit j.val = true ∧ translateIndex 0 1 j.val = j.val+2 := by
  decide +kernel

/-- Finite mask facts identify the unique source position of an x-rotation output bit. -/
theorem x_mask_certificate : ∀ x : Fin 15, ∀ j : Fin 90,
    if (lowX x.val).testBit j.val then
      (highX x.val).testBit j.val = false ∧ translateIndex x.val 0 j.val = j.val+3*x.val
    else (highX x.val).testBit j.val = true ∧ 45-3*x.val ≤ j.val ∧
      translateIndex x.val 0 j.val = j.val-(45-3*x.val) := by
  decide +kernel

/-- A y rotation reads the corresponding permuted bit. -/
theorem yword_bit (v : Nat) (j : Fin 90) :
    (yword v).testBit j.val = v.testBit (translateIndex 0 1 j.val) := by
  have h := y_mask_certificate j
  simp only [yword, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_and, Nat.testBit_shiftRight]
  split at h
  · obtain ⟨hh, ht⟩ := h
    simp_all [Bool.and_eq_true, Nat.add_comm, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]
  · obtain ⟨hh, ht⟩ := h
    simp_all [Bool.and_eq_false_iff, Nat.add_comm, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

/-- An x rotation reads the corresponding permuted bit. -/
theorem xword_bit (v : Nat) (x : Fin 15) (j : Fin 90) :
    (xword v x.val).testBit j.val = v.testBit (translateIndex x.val 0 j.val) := by
  have h := x_mask_certificate x j
  simp only [xword, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_and, Nat.testBit_shiftRight]
  split at h
  · obtain ⟨hh, ht⟩ := h
    simp_all [Nat.add_comm]
  · obtain ⟨hh, hge, ht⟩ := h
    simp_all [Nat.add_comm]

/-- The y rotation stays inside the90-bit chain. -/
theorem yword_lt (v : Nat) : yword v < 2^90 := by
  unfold yword
  apply Nat.or_lt_two_pow
  · have h : v &&& lowY ≤ lowY := Nat.and_le_right
    rw [Nat.shiftLeft_eq]
    norm_num [lowY] at h ⊢
    omega
  · exact lt_of_le_of_lt Nat.and_le_right (by decide)

/-- The x rotation stays inside the90-bit chain. -/
theorem xword_lt (v : Nat) (x : Fin 15) : xword v x.val < 2^90 := by
  have h : ∀ x : Fin 15, lowX x.val < 2^90 ∧ highX x.val < 2^90 := by decide +kernel
  exact Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_right (h x).1)
    (lt_of_le_of_lt Nat.and_le_right (h x).2)

/-- A repeated lane mask for the batch operations. -/
noncomputable def rep (size : Nat) : Nat := packF 128 size (fun _ => 1)
/-- Rotate all y coordinates in a packed batch. -/
noncomputable def ybatch (r v : Nat) : Nat := ((v &&& (r*lowY)) <<< 1) ||| ((v >>> 2) &&& (r*highY))
/-- Rotate all x coordinates in a packed batch. -/
noncomputable def xbatch (r v x : Nat) : Nat :=
  ((v >>> (3*x)) &&& (r*lowX x)) ||| ((v <<< (45-3*x)) &&& (r*highX x))

/-- The batched y permutation is the scalar permutation in every lane. -/
theorem ybatch_eq (size : Nat) (f : Nat → Nat) (hf : ∀ i < size, f i < 2^90) :
    ybatch (rep size) (packF 128 size f) = packF 128 size (fun i => yword (f i)) := by
  have hf' : ∀ i < size, f i < 2^128 := fun i hi => lt_trans (hf i hi) (by norm_num)
  have hlo : lowY < 2^128 := by decide
  have hhi : highY < 2^128 := by decide
  have hlob : ∀ i < size, (f i &&& lowY) <<< 1 < 2^128 := by
    intro i hi
    have h := Nat.and_le_right (n := f i) (m := lowY)
    rw [Nat.shiftLeft_eq]
    norm_num [lowY] at h ⊢
    omega
  have hhib : ∀ i < size, (f i >>> 2) &&& highY < 2^128 :=
    fun _ _ => lt_of_le_of_lt Nat.and_le_right hhi
  simp only [ybatch, rep, repeat_mul_eq_packF]
  rw [packF_and 128 size f _ (by decide) hf' (fun _ _ => hlo), packF_shift_left,
    masked_shiftRight_packF 128 size 2 highY f (by decide) hf' hhi]
  · exact packF_or 128 size _ _ (by decide) hlob hhib
  · intro j hj hge
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le (by decide : highY < 2^126)
      (Nat.pow_le_pow_right (by decide) (by omega))

/-- The batched x permutation is the scalar permutation in every lane. -/
theorem xbatch_eq (size : Nat) (f : Nat → Nat) (hf : ∀ i < size, f i < 2^90) (x : Fin 15) :
    xbatch (rep size) (packF 128 size f) x.val =
      packF 128 size (fun i => xword (f i) x.val) := by
  have hf' : ∀ i < size, f i < 2^128 := fun i hi => lt_trans (hf i hi) (by norm_num)
  have hmask : ∀ x : Fin 15, lowX x.val < 2^128 ∧ highX x.val < 2^128 ∧
      (∀ j : Fin 128, 128 ≤ j.val+3*x.val → (lowX x.val).testBit j.val = false) ∧
      (∀ j : Fin 128, j.val < 45-3*x.val → (highX x.val).testBit j.val = false) := by
    decide +kernel
  simp only [xbatch, rep, repeat_mul_eq_packF]
  rw [masked_shiftRight_packF 128 size (3*x.val) (lowX x.val) f (by decide) hf' (hmask x).1
      (fun j hj hge => (hmask x).2.2.1 ⟨j,hj⟩ hge),
    masked_shiftLeft_packF 128 size (45-3*x.val) (highX x.val) f (by decide) hf' (hmask x).2.1
      (fun j hj hlt => (hmask x).2.2.2 ⟨j,hj⟩ hlt)]
  exact packF_or 128 size _ _ (by decide)
    (fun _ _ => lt_of_le_of_lt Nat.and_le_right (hmask x).1)
    (fun _ _ => lt_of_le_of_lt Nat.and_le_right (hmask x).2.1)

/-- The coordinate permutations preserve the90-bit index set and compose as expected. -/
theorem index_composition_certificate : ∀ x : Fin 15, ∀ j : Fin 90,
    translateIndex x.val 0 j.val < 90 ∧
    translateIndex 0 1 (translateIndex x.val 0 j.val) < 90 ∧
    translateIndex 0 1 (translateIndex x.val 0 j.val) = translateIndex x.val 1 j.val ∧
    translateIndex 0 1 (translateIndex 0 1 (translateIndex x.val 0 j.val)) =
      translateIndex x.val 2 j.val := by
  decide +kernel

/-- Apply one of the45 translations to a single word. -/
noncomputable def word (v x y : Nat) : Nat :=
  xword (if y = 0 then v else if y = 1 then yword v else yword (yword v)) x

/-- Apply one of the45 translations to all packed words. -/
noncomputable def batch (r v x y : Nat) : Nat :=
  xbatch r (if y = 0 then v else if y = 1 then ybatch r v else ybatch r (ybatch r v)) x

/-- Batched translations apply the scalar translation in every lane. -/
theorem batch_eq (size : Nat) (f : Nat → Nat) (hf : ∀ i < size, f i < 2^90)
    (x : Fin 15) (y : Fin 3) :
    batch (rep size) (packF 128 size f) x.val y.val =
      packF 128 size (fun i => word (f i) x.val y.val) := by
  fin_cases y <;> simp only [batch, word, Fin.val_zero, Fin.val_one, Fin.val_two,
    ↓reduceIte, Nat.reduceEqDiff]
  · exact xbatch_eq size f hf x
  · rw [ybatch_eq size f hf]
    exact xbatch_eq size _ (fun _ _ => yword_lt _) x
  · rw [ybatch_eq size f hf, ybatch_eq size _ (fun _ _ => yword_lt _)]
    exact xbatch_eq size _ (fun _ _ => yword_lt _) x

/-- Scalar translations coincide with the established packed-orbit entries. -/
theorem word_eq_entry (v : Nat) (hv : v < 2^90) (x : Fin 15) (y : Fin 3) :
    word v x.val y.val = entry (v % 2^45) (v / 2^45) (15*y.val+x.val) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 90
  · rw [entry_testBit hv x.isLt y.isLt hj]
    have hidx := index_composition_certificate x ⟨j,hj⟩
    fin_cases y <;> simp only [word, Fin.val_zero, Fin.val_one, Fin.val_two,
      ↓reduceIte, Nat.reduceEqDiff]
    · exact xword_bit v x ⟨j,hj⟩
    · rw [xword_bit _ x ⟨j,hj⟩, yword_bit v ⟨_,hidx.1⟩]
      exact congrArg (Nat.testBit v) hidx.2.2.1
    · rw [xword_bit _ x ⟨j,hj⟩, yword_bit _ ⟨_,hidx.1⟩,
        yword_bit v ⟨_,hidx.2.1⟩]
      exact congrArg (Nat.testBit v) hidx.2.2.2
  · unfold word
    have hp : 2^90 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (xword_lt _ x) hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (entry_lt _ _ _) hp)]

end Quantum.Stabilizer.Homological.GBOrbit.Batch

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchSemantics
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitFixedSum
import QEC.Stabilizer.Framework.Homological.Certificate.PackedEquality

noncomputable section

namespace Quantum.Stabilizer.Homological.GBOrbit.Batch
open PackedDigits

/-- Enumerate the45 batched translations with x varying fastest. -/
noncomputable def tr (r v i : Nat) : Nat := batch r v (i%15) (i/15)

/-- Every enumerated batch translation is the corresponding established orbit entry. -/
theorem tr_eq (size : Nat) (f : Nat → Nat) (hf : ∀ i < size, f i < 2^90)
    (i : Nat) (hi : i < 45) :
    tr (rep size) (packF 128 size f) i =
      packF 128 size (fun j => entry (f j%2^45) (f j/2^45) i) := by
  unfold tr
  rw [batch_eq size f hf ⟨i%15,Nat.mod_lt _ (by decide)⟩ ⟨i/15,by omega⟩]
  apply packF_congr
  intro j hj
  rw [word_eq_entry (f j) (hf j hj) ⟨i%15,Nat.mod_lt _ (by decide)⟩ ⟨i/15,by omega⟩]
  congr 1
  change 15*(i/15)+i%15=i
  have h := Nat.mod_add_div i 15
  omega

/-- The comparison sentinel is repeated independently in every batch lane. -/
theorem rep_sentinel (size bits : Nat) :
    rep size <<< bits = packF 128 size (fun _ => 2^bits) := by
  unfold rep
  rw [packF_shift_left]
  simp [Nat.shiftLeft_eq]

/-- Simultaneous numerical comparisons certify all scalar canonicality inequalities. -/
theorem canonical_of_batch_comparisons (size : Nat) (f : Nat → Nat)
    (hf : ∀ j < size, f j < 2^90)
    (hcheck : ∀ i < 45, ((tr (rep size) (packF 128 size f) i +
      (rep size <<< 90) - packF 128 size f) &&& (rep size <<< 90)) =
        (rep size <<< 90)) :
    ∀ j < size, ∀ i < 45, f j ≤ entry (f j%2^45) (f j/2^45) i := by
  intro j hj i hi
  have h := hcheck i hi
  rw [tr_eq size f hf i hi, rep_sentinel] at h
  exact packed_compare_tables 128 size 90 _ f (by decide)
    (fun _ _ => entry_lt _ _ _) hf h j hj

/-- Compare all lanes with one translated batch, returning zero-one equality flags. -/
noncomputable def flags (r v i : Nat) : Nat :=
  ((r <<< 90) ^^^ (((tr r v i ^^^ v)+r*(2^90-1)) &&& (r <<< 90))) >>> 90

/-- The equality flags are exact in every lane of every translation. -/
theorem flags_eq (size : Nat) (f : Nat → Nat) (hf : ∀ j < size, f j < 2^90)
    (i : Nat) (hi : i < 45) :
    flags (rep size) (packF 128 size f) i =
      packF 128 size (fun j => if entry (f j%2^45) (f j/2^45) i = f j then 1 else 0) := by
  unfold flags
  rw [tr_eq size f hf i hi, rep_sentinel]
  have hl : rep size * (2^90-1) = packF 128 size (fun _ => 2^90-1) := by
    exact repeat_mul_eq_packF 128 size (2^90-1)
  rw [hl]
  exact packed_equality_flags 128 size 90 _ f (by decide) (fun _ _ => entry_lt _ _ _) hf

/-- Accumulate the45 equality flags to obtain each orbit stabilizer's size. -/
noncomputable def fixedCounts (r v : Nat) : Nat :=
  (List.range 45).foldl (fun acc i => acc+flags r v i) 0

/-- The batched stabilizer counts equal the scalar fixed-point counts. -/
theorem fixedCounts_eq (size : Nat) (f : Nat → Nat) (hf : ∀ j < size, f j < 2^90) :
    fixedCounts (rep size) (packF 128 size f) =
      packF 128 size (fun j => fixedCount (fixedMask (f j))) := by
  let tables : List (Nat → Nat) := (List.range 45).map fun i j =>
    if entry (f j%2^45) (f j/2^45) i = f j then 1 else 0
  have hs : fixedCounts (rep size) (packF 128 size f) =
      ((List.range 45).map (flags (rep size) (packF 128 size f))).sum := by
    rw [List.sum_eq_foldl]
    simp [fixedCounts, List.foldl_map]
  rw [hs]
  have hm : ((List.range 45).map (flags (rep size) (packF 128 size f))) =
      tables.map (packF 128 size) := by
    simp only [tables, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    exact flags_eq size f hf i (List.mem_range.mp hi)
  rw [hm, packF_list_sum]
  apply packF_congr
  intro j hj
  rw [fixedCount_eq_sum (f j) (hf j hj)]
  simp only [tables, List.map_map, Function.comp_def]

end Quantum.Stabilizer.Homological.GBOrbit.Batch

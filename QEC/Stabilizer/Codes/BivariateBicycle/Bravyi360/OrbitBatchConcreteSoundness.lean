import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchCheck
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchSoundness
import QEC.Stabilizer.Framework.Homological.Certificate.PackedSequence
import QEC.Stabilizer.Framework.Homological.Certificate.PackedPopcount
import QEC.Stabilizer.Framework.Homological.Certificate.BatchLinear

noncomputable section

set_option maxRecDepth 100000

namespace OrbitBatchCheck
open PackedDigits
open Quantum.Stabilizer.Homological
open F2Mask

/-- The fast numerical orbit translation is the proved batched permutation. -/
theorem tr_semantics (r v i : Nat) : tr r v i = GBOrbit.Batch.tr r v i := rfl

/--
The seven fixed numerical popcount masks implement the generic pair-summing
tree.
-/
theorem popcount_semantics (r v : Nat) : popcount128 r v = PackedDigits.popcount128 r v := by
  rfl

/--
The extra checks prove payload bounds, the weight bound, and adjacent strict
order.
-/
theorem extraCheck_sound (size value : Nat) (hv : value < 2^(128*size))
    (h : extraCheck (packF 128 size (fun _ => 1)) value = true) :
    (∀ i < size, lane 128 i value < 2^90) ∧
    (∀ i < size, bitCount 90 (lane 128 i value) ≤ 22) ∧
    (∀ i, i+1 < size → lane 128 i value < lane 128 (i+1) value) := by
  let f := fun i => lane 128 i value
  have hf128 : ∀ i < size, f i < 2^128 := fun i _ => lane_lt 128 i value
  have he : value = packF 128 size f := (packF_lanes 128 size value (by decide) hv).symm
  rw [he] at h
  simp only [extraCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hfit,hw⟩,horder⟩ := h
  rw [repeat_mul_eq_packF] at hfit
  have hf := packed_mask_bound 128 size 90 f (by decide) hf128 hfit
  refine ⟨hf,?_,?_⟩
  · rw [popcount_semantics, popcount128_packF size f hf, repeat_mul_eq_packF,
      packF_shift_left] at hw
    simp only [Nat.shiftLeft_eq, Nat.one_mul] at hw
    exact packed_compare_tables 128 size 7 (fun _ => 22) (fun i => bitCount 90 (f i))
      (by decide) (fun _ _ => show 22 < 2^7 from by decide)
      (fun i _ => lt_of_le_of_lt (bitCount_le 90 (f i)) (by decide)) hw
  · intro i hi
    have hs : size = (size-1)+1 := by omega
    have hr : packF 128 size (fun _ => 1) >>> 128 =
        packF 128 (size-1) (fun _ => 1) := by
      rw [hs]
      exact packF_drop_one 128 (size-1) (fun _ => 1) (by decide) (fun _ _ => show 1 < 2^128 from by decide)
    rw [hr,hs] at horder
    have hadj := packed_adjacent_strict 128 (size-1) 90 f (by decide)
      (by simpa only [← hs] using hf) horder i (by omega)
    exact hadj

/--
An accepted numerical batch consists of canonical representatives with the
stated fixed counts.
-/
theorem batchCheck_sound (size value expected : Nat) (hv : value < 2^(128*size))
    (h : batchCheck (packF 128 size (fun _ => 1)) value expected = true) :
    (∀ i < size, lane 128 i value < 2^90) ∧
    (∀ i < size, bitCount 90 (lane 128 i value) ≤ 22) ∧
    (∀ i, i+1 < size → lane 128 i value < lane 128 (i+1) value) ∧
    (∀ i < size, ∀ t < 45, lane 128 i value ≤
      GBOrbit.entry (lane 128 i value % 2^45) (lane 128 i value / 2^45) t) ∧
    (∀ i < size, GBOrbit.fixedCount (GBOrbit.fixedMask (lane 128 i value)) = lane 128 i expected) := by
  have hp := h
  simp only [batchCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hextra,hcanonical⟩,hfixed⟩ := hp
  obtain ⟨hfit,hweight,horder⟩ := extraCheck_sound size value hv hextra
  let f := fun i => lane 128 i value
  have he : value = packF 128 size f := (packF_lanes 128 size value (by decide) hv).symm
  have hc : ∀ t < 45,
      (((GBOrbit.Batch.tr (GBOrbit.Batch.rep size) (packF 128 size f) t +
        (GBOrbit.Batch.rep size <<< 90) - packF 128 size f) &&&
          (GBOrbit.Batch.rep size <<< 90)) = GBOrbit.Batch.rep size <<< 90) := by
    intro t ht
    have hh := hcanonical t (List.mem_range.mpr ht)
    simpa only [he,tr_semantics,GBOrbit.Batch.rep] using hh
  refine ⟨hfit,hweight,horder,
    GBOrbit.Batch.canonical_of_batch_comparisons size f hfit hc,?_⟩
  have hfc : GBOrbit.Batch.fixedCounts (GBOrbit.Batch.rep size) (packF 128 size f) = expected := by
    simpa only [he,tr_semantics,GBOrbit.Batch.fixedCounts,GBOrbit.Batch.flags,GBOrbit.Batch.rep] using hfixed
  rw [GBOrbit.Batch.fixedCounts_eq size f hfit] at hfc
  intro i hi
  have hh := congrArg (lane 128 i) hfc
  rw [lane_packF] at hh
  · simpa [hi] using hh
  · intro j hj
    unfold GBOrbit.fixedCount
    have hc := Finset.card_filter_le (s := Finset.range 45)
      (p := fun k => (GBOrbit.fixedMask (f j)).testBit (128*k+90) = true)
    have hle : ((Finset.range 45).filter
      (fun k => (GBOrbit.fixedMask (f j)).testBit (128*k+90) = true)).card ≤ 45 := by simpa using hc
    exact lt_of_le_of_lt hle (by decide)

end OrbitBatchCheck

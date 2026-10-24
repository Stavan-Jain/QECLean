import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchMetadata
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchConcreteSoundness
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.GBReflectedAction
import Mathlib.Order.Fin.Basic

noncomputable section

namespace OrbitBatchData
open PackedDigits
open Quantum.Stabilizer.Homological
open F2Mask

/-- All finite orbit checks have their pointwise semantic meaning in every stored batch. -/
theorem checked_properties (b : Fin 268) :
    (∀ i < sizeAt b.val, lane 128 i (wordsAt b.val) < 2^90) ∧
    (∀ i < sizeAt b.val, bitCount 90 (lane 128 i (wordsAt b.val)) ≤ 22) ∧
    (∀ i, i+1 < sizeAt b.val → lane 128 i (wordsAt b.val) < lane 128 (i+1) (wordsAt b.val)) ∧
    (∀ i < sizeAt b.val, ∀ t < 45, lane 128 i (wordsAt b.val) ≤
      GBOrbit.entry (lane 128 i (wordsAt b.val) % 2^45) (lane 128 i (wordsAt b.val) / 2^45) t) ∧
    (∀ i < sizeAt b.val, GBOrbit.fixedCount (GBOrbit.fixedMask (lane 128 i (wordsAt b.val))) =
      fixedAt (1024*b.val+i)) := by
  have h := all_checked b
  rw [repeat_size_eq] at h
  obtain ⟨hf,hw,hs,hc,hfcount⟩ := OrbitBatchCheck.batchCheck_sound
    (sizeAt b.val) (wordsAt b.val) (expectedAt b.val) (words_bounded b) h
  refine ⟨hf,hw,hs,hc,?_⟩
  intro i hi
  rw [hfcount i hi,expected_eq b,lane_packF]
  · simp [hi]
  · exact fun j hj => fixedAt_lt _

/-- Dividing a global census index locates a valid batch and lane. -/
theorem index_bounds (i : Nat) (hi : i < 274011) :
    i/1024 < 268 ∧ i%1024 < sizeAt (i/1024) := by
  have hm := Nat.mod_lt i (by decide : 0 < 1024)
  have he := Nat.mod_add_div i 1024
  unfold sizeAt
  split_ifs <;> omega

/-- Every canonical census entry is a90-bit mask. -/
theorem repAt_bounded (i : Fin 274011) : repAt i.val < 2^90 := by
  have hb := index_bounds i.val i.isLt
  exact (checked_properties ⟨i.val/1024,hb.1⟩).1 (i.val%1024) hb.2

/-- Every canonical census entry has chain weight at most22. -/
theorem repAt_weight (i : Fin 274011) : bitCount 90 (repAt i.val) ≤ 22 := by
  have hb := index_bounds i.val i.isLt
  exact (checked_properties ⟨i.val/1024,hb.1⟩).2.1 (i.val%1024) hb.2

/-- Every canonical census entry minimizes its complete translation orbit. -/
theorem repAt_canonical (i : Fin 274011) : ∀ t < 45,
    repAt i.val ≤ GBOrbit.entry (repAt i.val%2^45) (repAt i.val/2^45) t := by
  have hb := index_bounds i.val i.isLt
  exact (checked_properties ⟨i.val/1024,hb.1⟩).2.2.2.1 (i.val%1024) hb.2

/-- The checked stabilizer count of each representative is the sparse expected value. -/
theorem repAt_fixed (i : Fin 274011) :
    GBOrbit.fixedCount (GBOrbit.fixedMask (repAt i.val)) = fixedAt i.val := by
  have hb := index_bounds i.val i.isLt
  have h := (checked_properties ⟨i.val/1024,hb.1⟩).2.2.2.2 (i.val%1024) hb.2
  have he := Nat.mod_add_div i.val 1024
  simpa only [show 1024*(i.val/1024)+i.val%1024=i.val by omega] using h

/-- Within-batch and cross-batch checks combine to prove adjacent global order. -/
theorem repAt_adjacent (i : Nat) (hi : i+1 < 274011) : repAt i < repAt (i+1) := by
  have hb := index_bounds i (by omega)
  have hb' := index_bounds (i+1) hi
  have hm := Nat.mod_lt i (by decide : 0 < 1024)
  have he := Nat.mod_add_div i 1024
  by_cases hend : i%1024 = 1023
  · have hb267 : i/1024 < 267 := by omega
    have hn : (i+1)/1024=i/1024+1 ∧ (i+1)%1024=0 := by omega
    simpa only [repAt,hend,hn.1,hn.2] using cross_sorted ⟨i/1024,hb267⟩
  · have hn : (i+1)/1024=i/1024 ∧ (i+1)%1024=i%1024+1 := by omega
    have hlane : i%1024+1 < sizeAt (i/1024) := by simpa only [hn.1,hn.2] using hb'.2
    have h := (checked_properties ⟨i/1024,hb.1⟩).2.2.1 (i%1024) hlane
    simpa only [repAt,hn.1,hn.2] using h

/-- The global canonical census is strictly increasing, hence has no repeated mask. -/
theorem repAt_strictMono : StrictMono (fun i : Fin 274011 => repAt i.val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact repAt_adjacent i.val (by have := i.isLt; omega)

end OrbitBatchData

/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/mark_research_noncomputable.py
Data and SHA-256 hashes: research_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchCheck
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchConcreteSoundness
import QEC.Stabilizer.Framework.Homological.Certificate.FiniteSumExceptions
import Mathlib.Tactic.FinCases

noncomputable section
set_option maxRecDepth 100000
namespace OrbitBatchData
open PackedDigits

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The fifteen nonzero representatives with a three-element translation stabilizer. -/
noncomputable def fixedThree : Finset Nat := {299,963,971,2941,26949,26959,58329,70679,110969,123726,136237,139734,150152,153236,268422}

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The certified stabilizer count at a global census index. -/
noncomputable def fixedAt (i : Nat) : Nat := if i = 0 then 45 else if i = 70587 then 9
  else if i ∈ fixedThree then 3 else 1

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The thirteen batches containing a nontrivial stabilizer. -/
noncomputable def specialBatches : Finset Nat := {0,2,26,56,68,69,108,120,133,136,146,149,262}

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- All other batches consist entirely of representatives with trivial stabilizers. -/
theorem fixedAt_regular (b j : Nat) (hb : b ∉ specialBatches) (hj : j < 1024) :
    fixedAt (1024*b+j) = 1 := by
  simp only [specialBatches, Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  simp only [fixedAt, fixedThree, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> omega

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every valid batch uses the proved 128-bit repetition constant. -/
theorem repeat_size_eq (b : Fin 268) :
    repeat128 (sizeAt b.val) = packF 128 (sizeAt b.val) (fun _ => 1) := by
  by_cases hb : b.val < 267
  · simpa [sizeAt,hb] using repeat1024_eq
  · have he : b.val = 267 := by omega
    simpa [sizeAt,he] using repeat603_eq

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every stabilizer count fits within one packed lane. -/
theorem fixedAt_lt (i : Nat) : fixedAt i < 2^128 := by
  unfold fixedAt
  split_ifs <;> decide

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 0 match their packed certificate. -/
theorem expected_special0 : expected0 = packF 128 1024 (fun j => fixedAt (1024*0+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 2 match their packed certificate. -/
theorem expected_special2 : expected2 = packF 128 1024 (fun j => fixedAt (1024*2+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 26 match their packed certificate. -/
theorem expected_special26 : expected26 = packF 128 1024 (fun j => fixedAt (1024*26+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 56 match their packed certificate. -/
theorem expected_special56 : expected56 = packF 128 1024 (fun j => fixedAt (1024*56+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 68 match their packed certificate. -/
theorem expected_special68 : expected68 = packF 128 1024 (fun j => fixedAt (1024*68+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 69 match their packed certificate. -/
theorem expected_special69 : expected69 = packF 128 1024 (fun j => fixedAt (1024*69+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 108 match their packed certificate. -/
theorem expected_special108 : expected108 = packF 128 1024 (fun j => fixedAt (1024*108+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 120 match their packed certificate. -/
theorem expected_special120 : expected120 = packF 128 1024 (fun j => fixedAt (1024*120+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 133 match their packed certificate. -/
theorem expected_special133 : expected133 = packF 128 1024 (fun j => fixedAt (1024*133+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 136 match their packed certificate. -/
theorem expected_special136 : expected136 = packF 128 1024 (fun j => fixedAt (1024*136+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 146 match their packed certificate. -/
theorem expected_special146 : expected146 = packF 128 1024 (fun j => fixedAt (1024*146+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 149 match their packed certificate. -/
theorem expected_special149 : expected149 = packF 128 1024 (fun j => fixedAt (1024*149+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional fixed counts in batch 262 match their packed certificate. -/
theorem expected_special262 : expected262 = packF 128 1024 (fun j => fixedAt (1024*262+j)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every ordinary expected-count word is the repetition word. -/
theorem expected_regular (b : Fin 268) (hb : b.val ∉ specialBatches) :
    expectedAt b.val = repeat128 (sizeAt b.val) := by
  fin_cases b
  · exact False.elim (hb (by decide))
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hb (by decide))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The expected packed stabilizer counts agree with their sparse global description. -/
theorem expected_eq (b : Fin 268) :
    expectedAt b.val = packF 128 (sizeAt b.val) (fun j => fixedAt (1024*b.val+j)) := by
  by_cases hb : b.val ∈ specialBatches
  · simp only [specialBatches, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · have he : b = 0 := Fin.ext hb
      subst b
      exact expected_special0
    · have he : b = 2 := Fin.ext hb
      subst b
      exact expected_special2
    · have he : b = 26 := Fin.ext hb
      subst b
      exact expected_special26
    · have he : b = 56 := Fin.ext hb
      subst b
      exact expected_special56
    · have he : b = 68 := Fin.ext hb
      subst b
      exact expected_special68
    · have he : b = 69 := Fin.ext hb
      subst b
      exact expected_special69
    · have he : b = 108 := Fin.ext hb
      subst b
      exact expected_special108
    · have he : b = 120 := Fin.ext hb
      subst b
      exact expected_special120
    · have he : b = 133 := Fin.ext hb
      subst b
      exact expected_special133
    · have he : b = 136 := Fin.ext hb
      subst b
      exact expected_special136
    · have he : b = 146 := Fin.ext hb
      subst b
      exact expected_special146
    · have he : b = 149 := Fin.ext hb
      subst b
      exact expected_special149
    · have he : b = 262 := Fin.ext hb
      subst b
      exact expected_special262
  · rw [expected_regular b hb, repeat_size_eq]
    apply packF_congr
    intro j hj
    have hj' : j < 1024 := by
      unfold sizeAt at hj
      split_ifs at hj <;> omega
    exact (fixedAt_regular b.val j hb hj').symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 0 and 1 are strictly separated. -/
theorem cross_sorted0 : lane 128 1023 words0 < lane 128 0 words1 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 1 and 2 are strictly separated. -/
theorem cross_sorted1 : lane 128 1023 words1 < lane 128 0 words2 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 2 and 3 are strictly separated. -/
theorem cross_sorted2 : lane 128 1023 words2 < lane 128 0 words3 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 3 and 4 are strictly separated. -/
theorem cross_sorted3 : lane 128 1023 words3 < lane 128 0 words4 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 4 and 5 are strictly separated. -/
theorem cross_sorted4 : lane 128 1023 words4 < lane 128 0 words5 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 5 and 6 are strictly separated. -/
theorem cross_sorted5 : lane 128 1023 words5 < lane 128 0 words6 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 6 and 7 are strictly separated. -/
theorem cross_sorted6 : lane 128 1023 words6 < lane 128 0 words7 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 7 and 8 are strictly separated. -/
theorem cross_sorted7 : lane 128 1023 words7 < lane 128 0 words8 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 8 and 9 are strictly separated. -/
theorem cross_sorted8 : lane 128 1023 words8 < lane 128 0 words9 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 9 and 10 are strictly separated. -/
theorem cross_sorted9 : lane 128 1023 words9 < lane 128 0 words10 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 10 and 11 are strictly separated. -/
theorem cross_sorted10 : lane 128 1023 words10 < lane 128 0 words11 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 11 and 12 are strictly separated. -/
theorem cross_sorted11 : lane 128 1023 words11 < lane 128 0 words12 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 12 and 13 are strictly separated. -/
theorem cross_sorted12 : lane 128 1023 words12 < lane 128 0 words13 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 13 and 14 are strictly separated. -/
theorem cross_sorted13 : lane 128 1023 words13 < lane 128 0 words14 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 14 and 15 are strictly separated. -/
theorem cross_sorted14 : lane 128 1023 words14 < lane 128 0 words15 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 15 and 16 are strictly separated. -/
theorem cross_sorted15 : lane 128 1023 words15 < lane 128 0 words16 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 16 and 17 are strictly separated. -/
theorem cross_sorted16 : lane 128 1023 words16 < lane 128 0 words17 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 17 and 18 are strictly separated. -/
theorem cross_sorted17 : lane 128 1023 words17 < lane 128 0 words18 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 18 and 19 are strictly separated. -/
theorem cross_sorted18 : lane 128 1023 words18 < lane 128 0 words19 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 19 and 20 are strictly separated. -/
theorem cross_sorted19 : lane 128 1023 words19 < lane 128 0 words20 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 20 and 21 are strictly separated. -/
theorem cross_sorted20 : lane 128 1023 words20 < lane 128 0 words21 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 21 and 22 are strictly separated. -/
theorem cross_sorted21 : lane 128 1023 words21 < lane 128 0 words22 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 22 and 23 are strictly separated. -/
theorem cross_sorted22 : lane 128 1023 words22 < lane 128 0 words23 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 23 and 24 are strictly separated. -/
theorem cross_sorted23 : lane 128 1023 words23 < lane 128 0 words24 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 24 and 25 are strictly separated. -/
theorem cross_sorted24 : lane 128 1023 words24 < lane 128 0 words25 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 25 and 26 are strictly separated. -/
theorem cross_sorted25 : lane 128 1023 words25 < lane 128 0 words26 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 26 and 27 are strictly separated. -/
theorem cross_sorted26 : lane 128 1023 words26 < lane 128 0 words27 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 27 and 28 are strictly separated. -/
theorem cross_sorted27 : lane 128 1023 words27 < lane 128 0 words28 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 28 and 29 are strictly separated. -/
theorem cross_sorted28 : lane 128 1023 words28 < lane 128 0 words29 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 29 and 30 are strictly separated. -/
theorem cross_sorted29 : lane 128 1023 words29 < lane 128 0 words30 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 30 and 31 are strictly separated. -/
theorem cross_sorted30 : lane 128 1023 words30 < lane 128 0 words31 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 31 and 32 are strictly separated. -/
theorem cross_sorted31 : lane 128 1023 words31 < lane 128 0 words32 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 32 and 33 are strictly separated. -/
theorem cross_sorted32 : lane 128 1023 words32 < lane 128 0 words33 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 33 and 34 are strictly separated. -/
theorem cross_sorted33 : lane 128 1023 words33 < lane 128 0 words34 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 34 and 35 are strictly separated. -/
theorem cross_sorted34 : lane 128 1023 words34 < lane 128 0 words35 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 35 and 36 are strictly separated. -/
theorem cross_sorted35 : lane 128 1023 words35 < lane 128 0 words36 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 36 and 37 are strictly separated. -/
theorem cross_sorted36 : lane 128 1023 words36 < lane 128 0 words37 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 37 and 38 are strictly separated. -/
theorem cross_sorted37 : lane 128 1023 words37 < lane 128 0 words38 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 38 and 39 are strictly separated. -/
theorem cross_sorted38 : lane 128 1023 words38 < lane 128 0 words39 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 39 and 40 are strictly separated. -/
theorem cross_sorted39 : lane 128 1023 words39 < lane 128 0 words40 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 40 and 41 are strictly separated. -/
theorem cross_sorted40 : lane 128 1023 words40 < lane 128 0 words41 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 41 and 42 are strictly separated. -/
theorem cross_sorted41 : lane 128 1023 words41 < lane 128 0 words42 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 42 and 43 are strictly separated. -/
theorem cross_sorted42 : lane 128 1023 words42 < lane 128 0 words43 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 43 and 44 are strictly separated. -/
theorem cross_sorted43 : lane 128 1023 words43 < lane 128 0 words44 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 44 and 45 are strictly separated. -/
theorem cross_sorted44 : lane 128 1023 words44 < lane 128 0 words45 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 45 and 46 are strictly separated. -/
theorem cross_sorted45 : lane 128 1023 words45 < lane 128 0 words46 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 46 and 47 are strictly separated. -/
theorem cross_sorted46 : lane 128 1023 words46 < lane 128 0 words47 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 47 and 48 are strictly separated. -/
theorem cross_sorted47 : lane 128 1023 words47 < lane 128 0 words48 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 48 and 49 are strictly separated. -/
theorem cross_sorted48 : lane 128 1023 words48 < lane 128 0 words49 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 49 and 50 are strictly separated. -/
theorem cross_sorted49 : lane 128 1023 words49 < lane 128 0 words50 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 50 and 51 are strictly separated. -/
theorem cross_sorted50 : lane 128 1023 words50 < lane 128 0 words51 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 51 and 52 are strictly separated. -/
theorem cross_sorted51 : lane 128 1023 words51 < lane 128 0 words52 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 52 and 53 are strictly separated. -/
theorem cross_sorted52 : lane 128 1023 words52 < lane 128 0 words53 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 53 and 54 are strictly separated. -/
theorem cross_sorted53 : lane 128 1023 words53 < lane 128 0 words54 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 54 and 55 are strictly separated. -/
theorem cross_sorted54 : lane 128 1023 words54 < lane 128 0 words55 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 55 and 56 are strictly separated. -/
theorem cross_sorted55 : lane 128 1023 words55 < lane 128 0 words56 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 56 and 57 are strictly separated. -/
theorem cross_sorted56 : lane 128 1023 words56 < lane 128 0 words57 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 57 and 58 are strictly separated. -/
theorem cross_sorted57 : lane 128 1023 words57 < lane 128 0 words58 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 58 and 59 are strictly separated. -/
theorem cross_sorted58 : lane 128 1023 words58 < lane 128 0 words59 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 59 and 60 are strictly separated. -/
theorem cross_sorted59 : lane 128 1023 words59 < lane 128 0 words60 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 60 and 61 are strictly separated. -/
theorem cross_sorted60 : lane 128 1023 words60 < lane 128 0 words61 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 61 and 62 are strictly separated. -/
theorem cross_sorted61 : lane 128 1023 words61 < lane 128 0 words62 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 62 and 63 are strictly separated. -/
theorem cross_sorted62 : lane 128 1023 words62 < lane 128 0 words63 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 63 and 64 are strictly separated. -/
theorem cross_sorted63 : lane 128 1023 words63 < lane 128 0 words64 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 64 and 65 are strictly separated. -/
theorem cross_sorted64 : lane 128 1023 words64 < lane 128 0 words65 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 65 and 66 are strictly separated. -/
theorem cross_sorted65 : lane 128 1023 words65 < lane 128 0 words66 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 66 and 67 are strictly separated. -/
theorem cross_sorted66 : lane 128 1023 words66 < lane 128 0 words67 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 67 and 68 are strictly separated. -/
theorem cross_sorted67 : lane 128 1023 words67 < lane 128 0 words68 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 68 and 69 are strictly separated. -/
theorem cross_sorted68 : lane 128 1023 words68 < lane 128 0 words69 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 69 and 70 are strictly separated. -/
theorem cross_sorted69 : lane 128 1023 words69 < lane 128 0 words70 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 70 and 71 are strictly separated. -/
theorem cross_sorted70 : lane 128 1023 words70 < lane 128 0 words71 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 71 and 72 are strictly separated. -/
theorem cross_sorted71 : lane 128 1023 words71 < lane 128 0 words72 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 72 and 73 are strictly separated. -/
theorem cross_sorted72 : lane 128 1023 words72 < lane 128 0 words73 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 73 and 74 are strictly separated. -/
theorem cross_sorted73 : lane 128 1023 words73 < lane 128 0 words74 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 74 and 75 are strictly separated. -/
theorem cross_sorted74 : lane 128 1023 words74 < lane 128 0 words75 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 75 and 76 are strictly separated. -/
theorem cross_sorted75 : lane 128 1023 words75 < lane 128 0 words76 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 76 and 77 are strictly separated. -/
theorem cross_sorted76 : lane 128 1023 words76 < lane 128 0 words77 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 77 and 78 are strictly separated. -/
theorem cross_sorted77 : lane 128 1023 words77 < lane 128 0 words78 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 78 and 79 are strictly separated. -/
theorem cross_sorted78 : lane 128 1023 words78 < lane 128 0 words79 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 79 and 80 are strictly separated. -/
theorem cross_sorted79 : lane 128 1023 words79 < lane 128 0 words80 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 80 and 81 are strictly separated. -/
theorem cross_sorted80 : lane 128 1023 words80 < lane 128 0 words81 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 81 and 82 are strictly separated. -/
theorem cross_sorted81 : lane 128 1023 words81 < lane 128 0 words82 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 82 and 83 are strictly separated. -/
theorem cross_sorted82 : lane 128 1023 words82 < lane 128 0 words83 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 83 and 84 are strictly separated. -/
theorem cross_sorted83 : lane 128 1023 words83 < lane 128 0 words84 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 84 and 85 are strictly separated. -/
theorem cross_sorted84 : lane 128 1023 words84 < lane 128 0 words85 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 85 and 86 are strictly separated. -/
theorem cross_sorted85 : lane 128 1023 words85 < lane 128 0 words86 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 86 and 87 are strictly separated. -/
theorem cross_sorted86 : lane 128 1023 words86 < lane 128 0 words87 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 87 and 88 are strictly separated. -/
theorem cross_sorted87 : lane 128 1023 words87 < lane 128 0 words88 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 88 and 89 are strictly separated. -/
theorem cross_sorted88 : lane 128 1023 words88 < lane 128 0 words89 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 89 and 90 are strictly separated. -/
theorem cross_sorted89 : lane 128 1023 words89 < lane 128 0 words90 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 90 and 91 are strictly separated. -/
theorem cross_sorted90 : lane 128 1023 words90 < lane 128 0 words91 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 91 and 92 are strictly separated. -/
theorem cross_sorted91 : lane 128 1023 words91 < lane 128 0 words92 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 92 and 93 are strictly separated. -/
theorem cross_sorted92 : lane 128 1023 words92 < lane 128 0 words93 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 93 and 94 are strictly separated. -/
theorem cross_sorted93 : lane 128 1023 words93 < lane 128 0 words94 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 94 and 95 are strictly separated. -/
theorem cross_sorted94 : lane 128 1023 words94 < lane 128 0 words95 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 95 and 96 are strictly separated. -/
theorem cross_sorted95 : lane 128 1023 words95 < lane 128 0 words96 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 96 and 97 are strictly separated. -/
theorem cross_sorted96 : lane 128 1023 words96 < lane 128 0 words97 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 97 and 98 are strictly separated. -/
theorem cross_sorted97 : lane 128 1023 words97 < lane 128 0 words98 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 98 and 99 are strictly separated. -/
theorem cross_sorted98 : lane 128 1023 words98 < lane 128 0 words99 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 99 and 100 are strictly separated. -/
theorem cross_sorted99 : lane 128 1023 words99 < lane 128 0 words100 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 100 and 101 are strictly separated. -/
theorem cross_sorted100 : lane 128 1023 words100 < lane 128 0 words101 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 101 and 102 are strictly separated. -/
theorem cross_sorted101 : lane 128 1023 words101 < lane 128 0 words102 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 102 and 103 are strictly separated. -/
theorem cross_sorted102 : lane 128 1023 words102 < lane 128 0 words103 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 103 and 104 are strictly separated. -/
theorem cross_sorted103 : lane 128 1023 words103 < lane 128 0 words104 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 104 and 105 are strictly separated. -/
theorem cross_sorted104 : lane 128 1023 words104 < lane 128 0 words105 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 105 and 106 are strictly separated. -/
theorem cross_sorted105 : lane 128 1023 words105 < lane 128 0 words106 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 106 and 107 are strictly separated. -/
theorem cross_sorted106 : lane 128 1023 words106 < lane 128 0 words107 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 107 and 108 are strictly separated. -/
theorem cross_sorted107 : lane 128 1023 words107 < lane 128 0 words108 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 108 and 109 are strictly separated. -/
theorem cross_sorted108 : lane 128 1023 words108 < lane 128 0 words109 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 109 and 110 are strictly separated. -/
theorem cross_sorted109 : lane 128 1023 words109 < lane 128 0 words110 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 110 and 111 are strictly separated. -/
theorem cross_sorted110 : lane 128 1023 words110 < lane 128 0 words111 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 111 and 112 are strictly separated. -/
theorem cross_sorted111 : lane 128 1023 words111 < lane 128 0 words112 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 112 and 113 are strictly separated. -/
theorem cross_sorted112 : lane 128 1023 words112 < lane 128 0 words113 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 113 and 114 are strictly separated. -/
theorem cross_sorted113 : lane 128 1023 words113 < lane 128 0 words114 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 114 and 115 are strictly separated. -/
theorem cross_sorted114 : lane 128 1023 words114 < lane 128 0 words115 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 115 and 116 are strictly separated. -/
theorem cross_sorted115 : lane 128 1023 words115 < lane 128 0 words116 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 116 and 117 are strictly separated. -/
theorem cross_sorted116 : lane 128 1023 words116 < lane 128 0 words117 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 117 and 118 are strictly separated. -/
theorem cross_sorted117 : lane 128 1023 words117 < lane 128 0 words118 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 118 and 119 are strictly separated. -/
theorem cross_sorted118 : lane 128 1023 words118 < lane 128 0 words119 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 119 and 120 are strictly separated. -/
theorem cross_sorted119 : lane 128 1023 words119 < lane 128 0 words120 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 120 and 121 are strictly separated. -/
theorem cross_sorted120 : lane 128 1023 words120 < lane 128 0 words121 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 121 and 122 are strictly separated. -/
theorem cross_sorted121 : lane 128 1023 words121 < lane 128 0 words122 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 122 and 123 are strictly separated. -/
theorem cross_sorted122 : lane 128 1023 words122 < lane 128 0 words123 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 123 and 124 are strictly separated. -/
theorem cross_sorted123 : lane 128 1023 words123 < lane 128 0 words124 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 124 and 125 are strictly separated. -/
theorem cross_sorted124 : lane 128 1023 words124 < lane 128 0 words125 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 125 and 126 are strictly separated. -/
theorem cross_sorted125 : lane 128 1023 words125 < lane 128 0 words126 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 126 and 127 are strictly separated. -/
theorem cross_sorted126 : lane 128 1023 words126 < lane 128 0 words127 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 127 and 128 are strictly separated. -/
theorem cross_sorted127 : lane 128 1023 words127 < lane 128 0 words128 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 128 and 129 are strictly separated. -/
theorem cross_sorted128 : lane 128 1023 words128 < lane 128 0 words129 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 129 and 130 are strictly separated. -/
theorem cross_sorted129 : lane 128 1023 words129 < lane 128 0 words130 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 130 and 131 are strictly separated. -/
theorem cross_sorted130 : lane 128 1023 words130 < lane 128 0 words131 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 131 and 132 are strictly separated. -/
theorem cross_sorted131 : lane 128 1023 words131 < lane 128 0 words132 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 132 and 133 are strictly separated. -/
theorem cross_sorted132 : lane 128 1023 words132 < lane 128 0 words133 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 133 and 134 are strictly separated. -/
theorem cross_sorted133 : lane 128 1023 words133 < lane 128 0 words134 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 134 and 135 are strictly separated. -/
theorem cross_sorted134 : lane 128 1023 words134 < lane 128 0 words135 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 135 and 136 are strictly separated. -/
theorem cross_sorted135 : lane 128 1023 words135 < lane 128 0 words136 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 136 and 137 are strictly separated. -/
theorem cross_sorted136 : lane 128 1023 words136 < lane 128 0 words137 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 137 and 138 are strictly separated. -/
theorem cross_sorted137 : lane 128 1023 words137 < lane 128 0 words138 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 138 and 139 are strictly separated. -/
theorem cross_sorted138 : lane 128 1023 words138 < lane 128 0 words139 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 139 and 140 are strictly separated. -/
theorem cross_sorted139 : lane 128 1023 words139 < lane 128 0 words140 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 140 and 141 are strictly separated. -/
theorem cross_sorted140 : lane 128 1023 words140 < lane 128 0 words141 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 141 and 142 are strictly separated. -/
theorem cross_sorted141 : lane 128 1023 words141 < lane 128 0 words142 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 142 and 143 are strictly separated. -/
theorem cross_sorted142 : lane 128 1023 words142 < lane 128 0 words143 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 143 and 144 are strictly separated. -/
theorem cross_sorted143 : lane 128 1023 words143 < lane 128 0 words144 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 144 and 145 are strictly separated. -/
theorem cross_sorted144 : lane 128 1023 words144 < lane 128 0 words145 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 145 and 146 are strictly separated. -/
theorem cross_sorted145 : lane 128 1023 words145 < lane 128 0 words146 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 146 and 147 are strictly separated. -/
theorem cross_sorted146 : lane 128 1023 words146 < lane 128 0 words147 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 147 and 148 are strictly separated. -/
theorem cross_sorted147 : lane 128 1023 words147 < lane 128 0 words148 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 148 and 149 are strictly separated. -/
theorem cross_sorted148 : lane 128 1023 words148 < lane 128 0 words149 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 149 and 150 are strictly separated. -/
theorem cross_sorted149 : lane 128 1023 words149 < lane 128 0 words150 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 150 and 151 are strictly separated. -/
theorem cross_sorted150 : lane 128 1023 words150 < lane 128 0 words151 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 151 and 152 are strictly separated. -/
theorem cross_sorted151 : lane 128 1023 words151 < lane 128 0 words152 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 152 and 153 are strictly separated. -/
theorem cross_sorted152 : lane 128 1023 words152 < lane 128 0 words153 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 153 and 154 are strictly separated. -/
theorem cross_sorted153 : lane 128 1023 words153 < lane 128 0 words154 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 154 and 155 are strictly separated. -/
theorem cross_sorted154 : lane 128 1023 words154 < lane 128 0 words155 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 155 and 156 are strictly separated. -/
theorem cross_sorted155 : lane 128 1023 words155 < lane 128 0 words156 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 156 and 157 are strictly separated. -/
theorem cross_sorted156 : lane 128 1023 words156 < lane 128 0 words157 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 157 and 158 are strictly separated. -/
theorem cross_sorted157 : lane 128 1023 words157 < lane 128 0 words158 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 158 and 159 are strictly separated. -/
theorem cross_sorted158 : lane 128 1023 words158 < lane 128 0 words159 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 159 and 160 are strictly separated. -/
theorem cross_sorted159 : lane 128 1023 words159 < lane 128 0 words160 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 160 and 161 are strictly separated. -/
theorem cross_sorted160 : lane 128 1023 words160 < lane 128 0 words161 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 161 and 162 are strictly separated. -/
theorem cross_sorted161 : lane 128 1023 words161 < lane 128 0 words162 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 162 and 163 are strictly separated. -/
theorem cross_sorted162 : lane 128 1023 words162 < lane 128 0 words163 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 163 and 164 are strictly separated. -/
theorem cross_sorted163 : lane 128 1023 words163 < lane 128 0 words164 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 164 and 165 are strictly separated. -/
theorem cross_sorted164 : lane 128 1023 words164 < lane 128 0 words165 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 165 and 166 are strictly separated. -/
theorem cross_sorted165 : lane 128 1023 words165 < lane 128 0 words166 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 166 and 167 are strictly separated. -/
theorem cross_sorted166 : lane 128 1023 words166 < lane 128 0 words167 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 167 and 168 are strictly separated. -/
theorem cross_sorted167 : lane 128 1023 words167 < lane 128 0 words168 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 168 and 169 are strictly separated. -/
theorem cross_sorted168 : lane 128 1023 words168 < lane 128 0 words169 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 169 and 170 are strictly separated. -/
theorem cross_sorted169 : lane 128 1023 words169 < lane 128 0 words170 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 170 and 171 are strictly separated. -/
theorem cross_sorted170 : lane 128 1023 words170 < lane 128 0 words171 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 171 and 172 are strictly separated. -/
theorem cross_sorted171 : lane 128 1023 words171 < lane 128 0 words172 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 172 and 173 are strictly separated. -/
theorem cross_sorted172 : lane 128 1023 words172 < lane 128 0 words173 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 173 and 174 are strictly separated. -/
theorem cross_sorted173 : lane 128 1023 words173 < lane 128 0 words174 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 174 and 175 are strictly separated. -/
theorem cross_sorted174 : lane 128 1023 words174 < lane 128 0 words175 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 175 and 176 are strictly separated. -/
theorem cross_sorted175 : lane 128 1023 words175 < lane 128 0 words176 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 176 and 177 are strictly separated. -/
theorem cross_sorted176 : lane 128 1023 words176 < lane 128 0 words177 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 177 and 178 are strictly separated. -/
theorem cross_sorted177 : lane 128 1023 words177 < lane 128 0 words178 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 178 and 179 are strictly separated. -/
theorem cross_sorted178 : lane 128 1023 words178 < lane 128 0 words179 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 179 and 180 are strictly separated. -/
theorem cross_sorted179 : lane 128 1023 words179 < lane 128 0 words180 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 180 and 181 are strictly separated. -/
theorem cross_sorted180 : lane 128 1023 words180 < lane 128 0 words181 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 181 and 182 are strictly separated. -/
theorem cross_sorted181 : lane 128 1023 words181 < lane 128 0 words182 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 182 and 183 are strictly separated. -/
theorem cross_sorted182 : lane 128 1023 words182 < lane 128 0 words183 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 183 and 184 are strictly separated. -/
theorem cross_sorted183 : lane 128 1023 words183 < lane 128 0 words184 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 184 and 185 are strictly separated. -/
theorem cross_sorted184 : lane 128 1023 words184 < lane 128 0 words185 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 185 and 186 are strictly separated. -/
theorem cross_sorted185 : lane 128 1023 words185 < lane 128 0 words186 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 186 and 187 are strictly separated. -/
theorem cross_sorted186 : lane 128 1023 words186 < lane 128 0 words187 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 187 and 188 are strictly separated. -/
theorem cross_sorted187 : lane 128 1023 words187 < lane 128 0 words188 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 188 and 189 are strictly separated. -/
theorem cross_sorted188 : lane 128 1023 words188 < lane 128 0 words189 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 189 and 190 are strictly separated. -/
theorem cross_sorted189 : lane 128 1023 words189 < lane 128 0 words190 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 190 and 191 are strictly separated. -/
theorem cross_sorted190 : lane 128 1023 words190 < lane 128 0 words191 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 191 and 192 are strictly separated. -/
theorem cross_sorted191 : lane 128 1023 words191 < lane 128 0 words192 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 192 and 193 are strictly separated. -/
theorem cross_sorted192 : lane 128 1023 words192 < lane 128 0 words193 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 193 and 194 are strictly separated. -/
theorem cross_sorted193 : lane 128 1023 words193 < lane 128 0 words194 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 194 and 195 are strictly separated. -/
theorem cross_sorted194 : lane 128 1023 words194 < lane 128 0 words195 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 195 and 196 are strictly separated. -/
theorem cross_sorted195 : lane 128 1023 words195 < lane 128 0 words196 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 196 and 197 are strictly separated. -/
theorem cross_sorted196 : lane 128 1023 words196 < lane 128 0 words197 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 197 and 198 are strictly separated. -/
theorem cross_sorted197 : lane 128 1023 words197 < lane 128 0 words198 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 198 and 199 are strictly separated. -/
theorem cross_sorted198 : lane 128 1023 words198 < lane 128 0 words199 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 199 and 200 are strictly separated. -/
theorem cross_sorted199 : lane 128 1023 words199 < lane 128 0 words200 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 200 and 201 are strictly separated. -/
theorem cross_sorted200 : lane 128 1023 words200 < lane 128 0 words201 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 201 and 202 are strictly separated. -/
theorem cross_sorted201 : lane 128 1023 words201 < lane 128 0 words202 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 202 and 203 are strictly separated. -/
theorem cross_sorted202 : lane 128 1023 words202 < lane 128 0 words203 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 203 and 204 are strictly separated. -/
theorem cross_sorted203 : lane 128 1023 words203 < lane 128 0 words204 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 204 and 205 are strictly separated. -/
theorem cross_sorted204 : lane 128 1023 words204 < lane 128 0 words205 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 205 and 206 are strictly separated. -/
theorem cross_sorted205 : lane 128 1023 words205 < lane 128 0 words206 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 206 and 207 are strictly separated. -/
theorem cross_sorted206 : lane 128 1023 words206 < lane 128 0 words207 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 207 and 208 are strictly separated. -/
theorem cross_sorted207 : lane 128 1023 words207 < lane 128 0 words208 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 208 and 209 are strictly separated. -/
theorem cross_sorted208 : lane 128 1023 words208 < lane 128 0 words209 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 209 and 210 are strictly separated. -/
theorem cross_sorted209 : lane 128 1023 words209 < lane 128 0 words210 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 210 and 211 are strictly separated. -/
theorem cross_sorted210 : lane 128 1023 words210 < lane 128 0 words211 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 211 and 212 are strictly separated. -/
theorem cross_sorted211 : lane 128 1023 words211 < lane 128 0 words212 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 212 and 213 are strictly separated. -/
theorem cross_sorted212 : lane 128 1023 words212 < lane 128 0 words213 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 213 and 214 are strictly separated. -/
theorem cross_sorted213 : lane 128 1023 words213 < lane 128 0 words214 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 214 and 215 are strictly separated. -/
theorem cross_sorted214 : lane 128 1023 words214 < lane 128 0 words215 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 215 and 216 are strictly separated. -/
theorem cross_sorted215 : lane 128 1023 words215 < lane 128 0 words216 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 216 and 217 are strictly separated. -/
theorem cross_sorted216 : lane 128 1023 words216 < lane 128 0 words217 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 217 and 218 are strictly separated. -/
theorem cross_sorted217 : lane 128 1023 words217 < lane 128 0 words218 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 218 and 219 are strictly separated. -/
theorem cross_sorted218 : lane 128 1023 words218 < lane 128 0 words219 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 219 and 220 are strictly separated. -/
theorem cross_sorted219 : lane 128 1023 words219 < lane 128 0 words220 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 220 and 221 are strictly separated. -/
theorem cross_sorted220 : lane 128 1023 words220 < lane 128 0 words221 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 221 and 222 are strictly separated. -/
theorem cross_sorted221 : lane 128 1023 words221 < lane 128 0 words222 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 222 and 223 are strictly separated. -/
theorem cross_sorted222 : lane 128 1023 words222 < lane 128 0 words223 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 223 and 224 are strictly separated. -/
theorem cross_sorted223 : lane 128 1023 words223 < lane 128 0 words224 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 224 and 225 are strictly separated. -/
theorem cross_sorted224 : lane 128 1023 words224 < lane 128 0 words225 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 225 and 226 are strictly separated. -/
theorem cross_sorted225 : lane 128 1023 words225 < lane 128 0 words226 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 226 and 227 are strictly separated. -/
theorem cross_sorted226 : lane 128 1023 words226 < lane 128 0 words227 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 227 and 228 are strictly separated. -/
theorem cross_sorted227 : lane 128 1023 words227 < lane 128 0 words228 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 228 and 229 are strictly separated. -/
theorem cross_sorted228 : lane 128 1023 words228 < lane 128 0 words229 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 229 and 230 are strictly separated. -/
theorem cross_sorted229 : lane 128 1023 words229 < lane 128 0 words230 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 230 and 231 are strictly separated. -/
theorem cross_sorted230 : lane 128 1023 words230 < lane 128 0 words231 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 231 and 232 are strictly separated. -/
theorem cross_sorted231 : lane 128 1023 words231 < lane 128 0 words232 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 232 and 233 are strictly separated. -/
theorem cross_sorted232 : lane 128 1023 words232 < lane 128 0 words233 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 233 and 234 are strictly separated. -/
theorem cross_sorted233 : lane 128 1023 words233 < lane 128 0 words234 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 234 and 235 are strictly separated. -/
theorem cross_sorted234 : lane 128 1023 words234 < lane 128 0 words235 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 235 and 236 are strictly separated. -/
theorem cross_sorted235 : lane 128 1023 words235 < lane 128 0 words236 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 236 and 237 are strictly separated. -/
theorem cross_sorted236 : lane 128 1023 words236 < lane 128 0 words237 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 237 and 238 are strictly separated. -/
theorem cross_sorted237 : lane 128 1023 words237 < lane 128 0 words238 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 238 and 239 are strictly separated. -/
theorem cross_sorted238 : lane 128 1023 words238 < lane 128 0 words239 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 239 and 240 are strictly separated. -/
theorem cross_sorted239 : lane 128 1023 words239 < lane 128 0 words240 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 240 and 241 are strictly separated. -/
theorem cross_sorted240 : lane 128 1023 words240 < lane 128 0 words241 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 241 and 242 are strictly separated. -/
theorem cross_sorted241 : lane 128 1023 words241 < lane 128 0 words242 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 242 and 243 are strictly separated. -/
theorem cross_sorted242 : lane 128 1023 words242 < lane 128 0 words243 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 243 and 244 are strictly separated. -/
theorem cross_sorted243 : lane 128 1023 words243 < lane 128 0 words244 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 244 and 245 are strictly separated. -/
theorem cross_sorted244 : lane 128 1023 words244 < lane 128 0 words245 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 245 and 246 are strictly separated. -/
theorem cross_sorted245 : lane 128 1023 words245 < lane 128 0 words246 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 246 and 247 are strictly separated. -/
theorem cross_sorted246 : lane 128 1023 words246 < lane 128 0 words247 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 247 and 248 are strictly separated. -/
theorem cross_sorted247 : lane 128 1023 words247 < lane 128 0 words248 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 248 and 249 are strictly separated. -/
theorem cross_sorted248 : lane 128 1023 words248 < lane 128 0 words249 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 249 and 250 are strictly separated. -/
theorem cross_sorted249 : lane 128 1023 words249 < lane 128 0 words250 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 250 and 251 are strictly separated. -/
theorem cross_sorted250 : lane 128 1023 words250 < lane 128 0 words251 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 251 and 252 are strictly separated. -/
theorem cross_sorted251 : lane 128 1023 words251 < lane 128 0 words252 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 252 and 253 are strictly separated. -/
theorem cross_sorted252 : lane 128 1023 words252 < lane 128 0 words253 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 253 and 254 are strictly separated. -/
theorem cross_sorted253 : lane 128 1023 words253 < lane 128 0 words254 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 254 and 255 are strictly separated. -/
theorem cross_sorted254 : lane 128 1023 words254 < lane 128 0 words255 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 255 and 256 are strictly separated. -/
theorem cross_sorted255 : lane 128 1023 words255 < lane 128 0 words256 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 256 and 257 are strictly separated. -/
theorem cross_sorted256 : lane 128 1023 words256 < lane 128 0 words257 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 257 and 258 are strictly separated. -/
theorem cross_sorted257 : lane 128 1023 words257 < lane 128 0 words258 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 258 and 259 are strictly separated. -/
theorem cross_sorted258 : lane 128 1023 words258 < lane 128 0 words259 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 259 and 260 are strictly separated. -/
theorem cross_sorted259 : lane 128 1023 words259 < lane 128 0 words260 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 260 and 261 are strictly separated. -/
theorem cross_sorted260 : lane 128 1023 words260 < lane 128 0 words261 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 261 and 262 are strictly separated. -/
theorem cross_sorted261 : lane 128 1023 words261 < lane 128 0 words262 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 262 and 263 are strictly separated. -/
theorem cross_sorted262 : lane 128 1023 words262 < lane 128 0 words263 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 263 and 264 are strictly separated. -/
theorem cross_sorted263 : lane 128 1023 words263 < lane 128 0 words264 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 264 and 265 are strictly separated. -/
theorem cross_sorted264 : lane 128 1023 words264 < lane 128 0 words265 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 265 and 266 are strictly separated. -/
theorem cross_sorted265 : lane 128 1023 words265 < lane 128 0 words266 := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Adjacent packed batches 266 and 267 are strictly separated. -/
theorem cross_sorted266 : lane 128 1023 words266 < lane 128 0 words267 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Consecutive batches are strictly separated in natural mask order. -/
theorem cross_sorted (b : Fin 267) :
    lane 128 1023 (wordsAt b.val) < lane 128 0 (wordsAt (b.val+1)) := by
  fin_cases b
  · exact cross_sorted0
  · exact cross_sorted1
  · exact cross_sorted2
  · exact cross_sorted3
  · exact cross_sorted4
  · exact cross_sorted5
  · exact cross_sorted6
  · exact cross_sorted7
  · exact cross_sorted8
  · exact cross_sorted9
  · exact cross_sorted10
  · exact cross_sorted11
  · exact cross_sorted12
  · exact cross_sorted13
  · exact cross_sorted14
  · exact cross_sorted15
  · exact cross_sorted16
  · exact cross_sorted17
  · exact cross_sorted18
  · exact cross_sorted19
  · exact cross_sorted20
  · exact cross_sorted21
  · exact cross_sorted22
  · exact cross_sorted23
  · exact cross_sorted24
  · exact cross_sorted25
  · exact cross_sorted26
  · exact cross_sorted27
  · exact cross_sorted28
  · exact cross_sorted29
  · exact cross_sorted30
  · exact cross_sorted31
  · exact cross_sorted32
  · exact cross_sorted33
  · exact cross_sorted34
  · exact cross_sorted35
  · exact cross_sorted36
  · exact cross_sorted37
  · exact cross_sorted38
  · exact cross_sorted39
  · exact cross_sorted40
  · exact cross_sorted41
  · exact cross_sorted42
  · exact cross_sorted43
  · exact cross_sorted44
  · exact cross_sorted45
  · exact cross_sorted46
  · exact cross_sorted47
  · exact cross_sorted48
  · exact cross_sorted49
  · exact cross_sorted50
  · exact cross_sorted51
  · exact cross_sorted52
  · exact cross_sorted53
  · exact cross_sorted54
  · exact cross_sorted55
  · exact cross_sorted56
  · exact cross_sorted57
  · exact cross_sorted58
  · exact cross_sorted59
  · exact cross_sorted60
  · exact cross_sorted61
  · exact cross_sorted62
  · exact cross_sorted63
  · exact cross_sorted64
  · exact cross_sorted65
  · exact cross_sorted66
  · exact cross_sorted67
  · exact cross_sorted68
  · exact cross_sorted69
  · exact cross_sorted70
  · exact cross_sorted71
  · exact cross_sorted72
  · exact cross_sorted73
  · exact cross_sorted74
  · exact cross_sorted75
  · exact cross_sorted76
  · exact cross_sorted77
  · exact cross_sorted78
  · exact cross_sorted79
  · exact cross_sorted80
  · exact cross_sorted81
  · exact cross_sorted82
  · exact cross_sorted83
  · exact cross_sorted84
  · exact cross_sorted85
  · exact cross_sorted86
  · exact cross_sorted87
  · exact cross_sorted88
  · exact cross_sorted89
  · exact cross_sorted90
  · exact cross_sorted91
  · exact cross_sorted92
  · exact cross_sorted93
  · exact cross_sorted94
  · exact cross_sorted95
  · exact cross_sorted96
  · exact cross_sorted97
  · exact cross_sorted98
  · exact cross_sorted99
  · exact cross_sorted100
  · exact cross_sorted101
  · exact cross_sorted102
  · exact cross_sorted103
  · exact cross_sorted104
  · exact cross_sorted105
  · exact cross_sorted106
  · exact cross_sorted107
  · exact cross_sorted108
  · exact cross_sorted109
  · exact cross_sorted110
  · exact cross_sorted111
  · exact cross_sorted112
  · exact cross_sorted113
  · exact cross_sorted114
  · exact cross_sorted115
  · exact cross_sorted116
  · exact cross_sorted117
  · exact cross_sorted118
  · exact cross_sorted119
  · exact cross_sorted120
  · exact cross_sorted121
  · exact cross_sorted122
  · exact cross_sorted123
  · exact cross_sorted124
  · exact cross_sorted125
  · exact cross_sorted126
  · exact cross_sorted127
  · exact cross_sorted128
  · exact cross_sorted129
  · exact cross_sorted130
  · exact cross_sorted131
  · exact cross_sorted132
  · exact cross_sorted133
  · exact cross_sorted134
  · exact cross_sorted135
  · exact cross_sorted136
  · exact cross_sorted137
  · exact cross_sorted138
  · exact cross_sorted139
  · exact cross_sorted140
  · exact cross_sorted141
  · exact cross_sorted142
  · exact cross_sorted143
  · exact cross_sorted144
  · exact cross_sorted145
  · exact cross_sorted146
  · exact cross_sorted147
  · exact cross_sorted148
  · exact cross_sorted149
  · exact cross_sorted150
  · exact cross_sorted151
  · exact cross_sorted152
  · exact cross_sorted153
  · exact cross_sorted154
  · exact cross_sorted155
  · exact cross_sorted156
  · exact cross_sorted157
  · exact cross_sorted158
  · exact cross_sorted159
  · exact cross_sorted160
  · exact cross_sorted161
  · exact cross_sorted162
  · exact cross_sorted163
  · exact cross_sorted164
  · exact cross_sorted165
  · exact cross_sorted166
  · exact cross_sorted167
  · exact cross_sorted168
  · exact cross_sorted169
  · exact cross_sorted170
  · exact cross_sorted171
  · exact cross_sorted172
  · exact cross_sorted173
  · exact cross_sorted174
  · exact cross_sorted175
  · exact cross_sorted176
  · exact cross_sorted177
  · exact cross_sorted178
  · exact cross_sorted179
  · exact cross_sorted180
  · exact cross_sorted181
  · exact cross_sorted182
  · exact cross_sorted183
  · exact cross_sorted184
  · exact cross_sorted185
  · exact cross_sorted186
  · exact cross_sorted187
  · exact cross_sorted188
  · exact cross_sorted189
  · exact cross_sorted190
  · exact cross_sorted191
  · exact cross_sorted192
  · exact cross_sorted193
  · exact cross_sorted194
  · exact cross_sorted195
  · exact cross_sorted196
  · exact cross_sorted197
  · exact cross_sorted198
  · exact cross_sorted199
  · exact cross_sorted200
  · exact cross_sorted201
  · exact cross_sorted202
  · exact cross_sorted203
  · exact cross_sorted204
  · exact cross_sorted205
  · exact cross_sorted206
  · exact cross_sorted207
  · exact cross_sorted208
  · exact cross_sorted209
  · exact cross_sorted210
  · exact cross_sorted211
  · exact cross_sorted212
  · exact cross_sorted213
  · exact cross_sorted214
  · exact cross_sorted215
  · exact cross_sorted216
  · exact cross_sorted217
  · exact cross_sorted218
  · exact cross_sorted219
  · exact cross_sorted220
  · exact cross_sorted221
  · exact cross_sorted222
  · exact cross_sorted223
  · exact cross_sorted224
  · exact cross_sorted225
  · exact cross_sorted226
  · exact cross_sorted227
  · exact cross_sorted228
  · exact cross_sorted229
  · exact cross_sorted230
  · exact cross_sorted231
  · exact cross_sorted232
  · exact cross_sorted233
  · exact cross_sorted234
  · exact cross_sorted235
  · exact cross_sorted236
  · exact cross_sorted237
  · exact cross_sorted238
  · exact cross_sorted239
  · exact cross_sorted240
  · exact cross_sorted241
  · exact cross_sorted242
  · exact cross_sorted243
  · exact cross_sorted244
  · exact cross_sorted245
  · exact cross_sorted246
  · exact cross_sorted247
  · exact cross_sorted248
  · exact cross_sorted249
  · exact cross_sorted250
  · exact cross_sorted251
  · exact cross_sorted252
  · exact cross_sorted253
  · exact cross_sorted254
  · exact cross_sorted255
  · exact cross_sorted256
  · exact cross_sorted257
  · exact cross_sorted258
  · exact cross_sorted259
  · exact cross_sorted260
  · exact cross_sorted261
  · exact cross_sorted262
  · exact cross_sorted263
  · exact cross_sorted264
  · exact cross_sorted265
  · exact cross_sorted266

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every stored batch satisfies the same numerical checker. -/
theorem all_checked (b : Fin 268) :
    OrbitBatchCheck.batchCheck (repeat128 (sizeAt b.val)) (wordsAt b.val) (expectedAt b.val) = true := by
  fin_cases b
  · exact OrbitBatchCheck.checked0
  · exact OrbitBatchCheck.checked1
  · exact OrbitBatchCheck.checked2
  · exact OrbitBatchCheck.checked3
  · exact OrbitBatchCheck.checked4
  · exact OrbitBatchCheck.checked5
  · exact OrbitBatchCheck.checked6
  · exact OrbitBatchCheck.checked7
  · exact OrbitBatchCheck.checked8
  · exact OrbitBatchCheck.checked9
  · exact OrbitBatchCheck.checked10
  · exact OrbitBatchCheck.checked11
  · exact OrbitBatchCheck.checked12
  · exact OrbitBatchCheck.checked13
  · exact OrbitBatchCheck.checked14
  · exact OrbitBatchCheck.checked15
  · exact OrbitBatchCheck.checked16
  · exact OrbitBatchCheck.checked17
  · exact OrbitBatchCheck.checked18
  · exact OrbitBatchCheck.checked19
  · exact OrbitBatchCheck.checked20
  · exact OrbitBatchCheck.checked21
  · exact OrbitBatchCheck.checked22
  · exact OrbitBatchCheck.checked23
  · exact OrbitBatchCheck.checked24
  · exact OrbitBatchCheck.checked25
  · exact OrbitBatchCheck.checked26
  · exact OrbitBatchCheck.checked27
  · exact OrbitBatchCheck.checked28
  · exact OrbitBatchCheck.checked29
  · exact OrbitBatchCheck.checked30
  · exact OrbitBatchCheck.checked31
  · exact OrbitBatchCheck.checked32
  · exact OrbitBatchCheck.checked33
  · exact OrbitBatchCheck.checked34
  · exact OrbitBatchCheck.checked35
  · exact OrbitBatchCheck.checked36
  · exact OrbitBatchCheck.checked37
  · exact OrbitBatchCheck.checked38
  · exact OrbitBatchCheck.checked39
  · exact OrbitBatchCheck.checked40
  · exact OrbitBatchCheck.checked41
  · exact OrbitBatchCheck.checked42
  · exact OrbitBatchCheck.checked43
  · exact OrbitBatchCheck.checked44
  · exact OrbitBatchCheck.checked45
  · exact OrbitBatchCheck.checked46
  · exact OrbitBatchCheck.checked47
  · exact OrbitBatchCheck.checked48
  · exact OrbitBatchCheck.checked49
  · exact OrbitBatchCheck.checked50
  · exact OrbitBatchCheck.checked51
  · exact OrbitBatchCheck.checked52
  · exact OrbitBatchCheck.checked53
  · exact OrbitBatchCheck.checked54
  · exact OrbitBatchCheck.checked55
  · exact OrbitBatchCheck.checked56
  · exact OrbitBatchCheck.checked57
  · exact OrbitBatchCheck.checked58
  · exact OrbitBatchCheck.checked59
  · exact OrbitBatchCheck.checked60
  · exact OrbitBatchCheck.checked61
  · exact OrbitBatchCheck.checked62
  · exact OrbitBatchCheck.checked63
  · exact OrbitBatchCheck.checked64
  · exact OrbitBatchCheck.checked65
  · exact OrbitBatchCheck.checked66
  · exact OrbitBatchCheck.checked67
  · exact OrbitBatchCheck.checked68
  · exact OrbitBatchCheck.checked69
  · exact OrbitBatchCheck.checked70
  · exact OrbitBatchCheck.checked71
  · exact OrbitBatchCheck.checked72
  · exact OrbitBatchCheck.checked73
  · exact OrbitBatchCheck.checked74
  · exact OrbitBatchCheck.checked75
  · exact OrbitBatchCheck.checked76
  · exact OrbitBatchCheck.checked77
  · exact OrbitBatchCheck.checked78
  · exact OrbitBatchCheck.checked79
  · exact OrbitBatchCheck.checked80
  · exact OrbitBatchCheck.checked81
  · exact OrbitBatchCheck.checked82
  · exact OrbitBatchCheck.checked83
  · exact OrbitBatchCheck.checked84
  · exact OrbitBatchCheck.checked85
  · exact OrbitBatchCheck.checked86
  · exact OrbitBatchCheck.checked87
  · exact OrbitBatchCheck.checked88
  · exact OrbitBatchCheck.checked89
  · exact OrbitBatchCheck.checked90
  · exact OrbitBatchCheck.checked91
  · exact OrbitBatchCheck.checked92
  · exact OrbitBatchCheck.checked93
  · exact OrbitBatchCheck.checked94
  · exact OrbitBatchCheck.checked95
  · exact OrbitBatchCheck.checked96
  · exact OrbitBatchCheck.checked97
  · exact OrbitBatchCheck.checked98
  · exact OrbitBatchCheck.checked99
  · exact OrbitBatchCheck.checked100
  · exact OrbitBatchCheck.checked101
  · exact OrbitBatchCheck.checked102
  · exact OrbitBatchCheck.checked103
  · exact OrbitBatchCheck.checked104
  · exact OrbitBatchCheck.checked105
  · exact OrbitBatchCheck.checked106
  · exact OrbitBatchCheck.checked107
  · exact OrbitBatchCheck.checked108
  · exact OrbitBatchCheck.checked109
  · exact OrbitBatchCheck.checked110
  · exact OrbitBatchCheck.checked111
  · exact OrbitBatchCheck.checked112
  · exact OrbitBatchCheck.checked113
  · exact OrbitBatchCheck.checked114
  · exact OrbitBatchCheck.checked115
  · exact OrbitBatchCheck.checked116
  · exact OrbitBatchCheck.checked117
  · exact OrbitBatchCheck.checked118
  · exact OrbitBatchCheck.checked119
  · exact OrbitBatchCheck.checked120
  · exact OrbitBatchCheck.checked121
  · exact OrbitBatchCheck.checked122
  · exact OrbitBatchCheck.checked123
  · exact OrbitBatchCheck.checked124
  · exact OrbitBatchCheck.checked125
  · exact OrbitBatchCheck.checked126
  · exact OrbitBatchCheck.checked127
  · exact OrbitBatchCheck.checked128
  · exact OrbitBatchCheck.checked129
  · exact OrbitBatchCheck.checked130
  · exact OrbitBatchCheck.checked131
  · exact OrbitBatchCheck.checked132
  · exact OrbitBatchCheck.checked133
  · exact OrbitBatchCheck.checked134
  · exact OrbitBatchCheck.checked135
  · exact OrbitBatchCheck.checked136
  · exact OrbitBatchCheck.checked137
  · exact OrbitBatchCheck.checked138
  · exact OrbitBatchCheck.checked139
  · exact OrbitBatchCheck.checked140
  · exact OrbitBatchCheck.checked141
  · exact OrbitBatchCheck.checked142
  · exact OrbitBatchCheck.checked143
  · exact OrbitBatchCheck.checked144
  · exact OrbitBatchCheck.checked145
  · exact OrbitBatchCheck.checked146
  · exact OrbitBatchCheck.checked147
  · exact OrbitBatchCheck.checked148
  · exact OrbitBatchCheck.checked149
  · exact OrbitBatchCheck.checked150
  · exact OrbitBatchCheck.checked151
  · exact OrbitBatchCheck.checked152
  · exact OrbitBatchCheck.checked153
  · exact OrbitBatchCheck.checked154
  · exact OrbitBatchCheck.checked155
  · exact OrbitBatchCheck.checked156
  · exact OrbitBatchCheck.checked157
  · exact OrbitBatchCheck.checked158
  · exact OrbitBatchCheck.checked159
  · exact OrbitBatchCheck.checked160
  · exact OrbitBatchCheck.checked161
  · exact OrbitBatchCheck.checked162
  · exact OrbitBatchCheck.checked163
  · exact OrbitBatchCheck.checked164
  · exact OrbitBatchCheck.checked165
  · exact OrbitBatchCheck.checked166
  · exact OrbitBatchCheck.checked167
  · exact OrbitBatchCheck.checked168
  · exact OrbitBatchCheck.checked169
  · exact OrbitBatchCheck.checked170
  · exact OrbitBatchCheck.checked171
  · exact OrbitBatchCheck.checked172
  · exact OrbitBatchCheck.checked173
  · exact OrbitBatchCheck.checked174
  · exact OrbitBatchCheck.checked175
  · exact OrbitBatchCheck.checked176
  · exact OrbitBatchCheck.checked177
  · exact OrbitBatchCheck.checked178
  · exact OrbitBatchCheck.checked179
  · exact OrbitBatchCheck.checked180
  · exact OrbitBatchCheck.checked181
  · exact OrbitBatchCheck.checked182
  · exact OrbitBatchCheck.checked183
  · exact OrbitBatchCheck.checked184
  · exact OrbitBatchCheck.checked185
  · exact OrbitBatchCheck.checked186
  · exact OrbitBatchCheck.checked187
  · exact OrbitBatchCheck.checked188
  · exact OrbitBatchCheck.checked189
  · exact OrbitBatchCheck.checked190
  · exact OrbitBatchCheck.checked191
  · exact OrbitBatchCheck.checked192
  · exact OrbitBatchCheck.checked193
  · exact OrbitBatchCheck.checked194
  · exact OrbitBatchCheck.checked195
  · exact OrbitBatchCheck.checked196
  · exact OrbitBatchCheck.checked197
  · exact OrbitBatchCheck.checked198
  · exact OrbitBatchCheck.checked199
  · exact OrbitBatchCheck.checked200
  · exact OrbitBatchCheck.checked201
  · exact OrbitBatchCheck.checked202
  · exact OrbitBatchCheck.checked203
  · exact OrbitBatchCheck.checked204
  · exact OrbitBatchCheck.checked205
  · exact OrbitBatchCheck.checked206
  · exact OrbitBatchCheck.checked207
  · exact OrbitBatchCheck.checked208
  · exact OrbitBatchCheck.checked209
  · exact OrbitBatchCheck.checked210
  · exact OrbitBatchCheck.checked211
  · exact OrbitBatchCheck.checked212
  · exact OrbitBatchCheck.checked213
  · exact OrbitBatchCheck.checked214
  · exact OrbitBatchCheck.checked215
  · exact OrbitBatchCheck.checked216
  · exact OrbitBatchCheck.checked217
  · exact OrbitBatchCheck.checked218
  · exact OrbitBatchCheck.checked219
  · exact OrbitBatchCheck.checked220
  · exact OrbitBatchCheck.checked221
  · exact OrbitBatchCheck.checked222
  · exact OrbitBatchCheck.checked223
  · exact OrbitBatchCheck.checked224
  · exact OrbitBatchCheck.checked225
  · exact OrbitBatchCheck.checked226
  · exact OrbitBatchCheck.checked227
  · exact OrbitBatchCheck.checked228
  · exact OrbitBatchCheck.checked229
  · exact OrbitBatchCheck.checked230
  · exact OrbitBatchCheck.checked231
  · exact OrbitBatchCheck.checked232
  · exact OrbitBatchCheck.checked233
  · exact OrbitBatchCheck.checked234
  · exact OrbitBatchCheck.checked235
  · exact OrbitBatchCheck.checked236
  · exact OrbitBatchCheck.checked237
  · exact OrbitBatchCheck.checked238
  · exact OrbitBatchCheck.checked239
  · exact OrbitBatchCheck.checked240
  · exact OrbitBatchCheck.checked241
  · exact OrbitBatchCheck.checked242
  · exact OrbitBatchCheck.checked243
  · exact OrbitBatchCheck.checked244
  · exact OrbitBatchCheck.checked245
  · exact OrbitBatchCheck.checked246
  · exact OrbitBatchCheck.checked247
  · exact OrbitBatchCheck.checked248
  · exact OrbitBatchCheck.checked249
  · exact OrbitBatchCheck.checked250
  · exact OrbitBatchCheck.checked251
  · exact OrbitBatchCheck.checked252
  · exact OrbitBatchCheck.checked253
  · exact OrbitBatchCheck.checked254
  · exact OrbitBatchCheck.checked255
  · exact OrbitBatchCheck.checked256
  · exact OrbitBatchCheck.checked257
  · exact OrbitBatchCheck.checked258
  · exact OrbitBatchCheck.checked259
  · exact OrbitBatchCheck.checked260
  · exact OrbitBatchCheck.checked261
  · exact OrbitBatchCheck.checked262
  · exact OrbitBatchCheck.checked263
  · exact OrbitBatchCheck.checked264
  · exact OrbitBatchCheck.checked265
  · exact OrbitBatchCheck.checked266
  · exact OrbitBatchCheck.checked267
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The accepted payload mask bounds every stored word by its allocated lanes. -/
theorem words_bounded (b : Fin 268) : wordsAt b.val < 2^(128*sizeAt b.val) := by
  have h := all_checked b
  simp only [OrbitBatchCheck.batchCheck, Bool.and_eq_true, beq_iff_eq] at h
  have he := h.1.1
  simp only [OrbitBatchCheck.extraCheck, Bool.and_eq_true, beq_iff_eq] at he
  have hfit := he.1.1
  rw [repeat_size_eq b, repeat_mul_eq_packF] at hfit
  calc
    wordsAt b.val = wordsAt b.val &&& packF 128 (sizeAt b.val) (fun _ => 2^90-1) := hfit.symm
    _ ≤ packF 128 (sizeAt b.val) (fun _ => 2^90-1) := Nat.and_le_right
    _ < 2^(128*sizeAt b.val) := packF_lt 128 (sizeAt b.val) _ (by decide)
      (fun _ _ => show 2^90-1 < 2^128 from by decide)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The seventeen representatives with nontrivial translation stabilizer. -/
noncomputable def exceptional : Finset (Fin 274011) :=
  {0,299,963,971,2941,26949,26959,58329,70587,70679,110969,123726,136237,139734,150152,153236,268422}

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exceptional stabilizers contribute exactly231 distinct translated masks. -/
theorem exceptional_counts : exceptional.card = 17 ∧
    (∑ i ∈ exceptional, 45/fixedAt i.val) = 231 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every representative outside the short exceptional list has a full45-element orbit. -/
theorem fixedAt_of_not_exceptional (i : Fin 274011) (hi : i ∉ exceptional) : fixedAt i.val = 1 := by
  simp only [exceptional, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp only [fixedAt, fixedThree, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> simp_all only [Fin.ext_iff, Fin.val_natCast, Nat.reduceMod] <;> omega



end OrbitBatchData

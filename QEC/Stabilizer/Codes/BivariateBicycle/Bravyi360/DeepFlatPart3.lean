/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_deep_flat_batch.py
Data and SHA-256 hashes: root_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFlatBatch

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFlatData
open F2Mask
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection18 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 18) (LowCycleNormalization.maskAt j)
    let b := betaAt 18
    let t := tag18 j
    let k := DeepFlatBatch.ref18 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 18. -/
theorem checked18 (j : Fin 1954) :
    let a := Nat.xor (firstAt 18) (LowCycleNormalization.maskAt j)
    let b := betaAt 18
    let t := tag18 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection18 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref18 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection19 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 19) (LowCycleNormalization.maskAt j)
    let b := betaAt 19
    let t := tag19 j
    let k := DeepFlatBatch.ref19 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 19. -/
theorem checked19 (j : Fin 1954) :
    let a := Nat.xor (firstAt 19) (LowCycleNormalization.maskAt j)
    let b := betaAt 19
    let t := tag19 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection19 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref19 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection20 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 20) (LowCycleNormalization.maskAt j)
    let b := betaAt 20
    let t := tag20 j
    let k := DeepFlatBatch.ref20 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 20. -/
theorem checked20 (j : Fin 1954) :
    let a := Nat.xor (firstAt 20) (LowCycleNormalization.maskAt j)
    let b := betaAt 20
    let t := tag20 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection20 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref20 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection21 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 21) (LowCycleNormalization.maskAt j)
    let b := betaAt 21
    let t := tag21 j
    let k := DeepFlatBatch.ref21 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 21. -/
theorem checked21 (j : Fin 1954) :
    let a := Nat.xor (firstAt 21) (LowCycleNormalization.maskAt j)
    let b := betaAt 21
    let t := tag21 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection21 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref21 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection22 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 22) (LowCycleNormalization.maskAt j)
    let b := betaAt 22
    let t := tag22 j
    let k := DeepFlatBatch.ref22 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 22. -/
theorem checked22 (j : Fin 1954) :
    let a := Nat.xor (firstAt 22) (LowCycleNormalization.maskAt j)
    let b := betaAt 22
    let t := tag22 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection22 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref22 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection23 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 23) (LowCycleNormalization.maskAt j)
    let b := betaAt 23
    let t := tag23 j
    let k := DeepFlatBatch.ref23 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 23. -/
theorem checked23 (j : Fin 1954) :
    let a := Nat.xor (firstAt 23) (LowCycleNormalization.maskAt j)
    let b := betaAt 23
    let t := tag23 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection23 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref23 j, hk⟩
    simpa only [ha, hb, ht] using h
end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFlatData

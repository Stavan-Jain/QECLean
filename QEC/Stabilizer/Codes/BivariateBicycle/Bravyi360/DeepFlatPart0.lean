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
theorem selection0 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 0) (LowCycleNormalization.maskAt j)
    let b := betaAt 0
    let t := tag0 j
    let k := DeepFlatBatch.ref0 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 0. -/
theorem checked0 (j : Fin 1954) :
    let a := Nat.xor (firstAt 0) (LowCycleNormalization.maskAt j)
    let b := betaAt 0
    let t := tag0 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection0 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref0 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection1 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 1) (LowCycleNormalization.maskAt j)
    let b := betaAt 1
    let t := tag1 j
    let k := DeepFlatBatch.ref1 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 1. -/
theorem checked1 (j : Fin 1954) :
    let a := Nat.xor (firstAt 1) (LowCycleNormalization.maskAt j)
    let b := betaAt 1
    let t := tag1 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection1 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref1 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection2 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 2) (LowCycleNormalization.maskAt j)
    let b := betaAt 2
    let t := tag2 j
    let k := DeepFlatBatch.ref2 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 2. -/
theorem checked2 (j : Fin 1954) :
    let a := Nat.xor (firstAt 2) (LowCycleNormalization.maskAt j)
    let b := betaAt 2
    let t := tag2 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection2 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref2 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection3 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 3) (LowCycleNormalization.maskAt j)
    let b := betaAt 3
    let t := tag3 j
    let k := DeepFlatBatch.ref3 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 3. -/
theorem checked3 (j : Fin 1954) :
    let a := Nat.xor (firstAt 3) (LowCycleNormalization.maskAt j)
    let b := betaAt 3
    let t := tag3 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection3 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref3 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection4 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 4) (LowCycleNormalization.maskAt j)
    let b := betaAt 4
    let t := tag4 j
    let k := DeepFlatBatch.ref4 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 4. -/
theorem checked4 (j : Fin 1954) :
    let a := Nat.xor (firstAt 4) (LowCycleNormalization.maskAt j)
    let b := betaAt 4
    let t := tag4 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection4 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref4 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection5 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 5) (LowCycleNormalization.maskAt j)
    let b := betaAt 5
    let t := tag5 j
    let k := DeepFlatBatch.ref5 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 5. -/
theorem checked5 (j : Fin 1954) :
    let a := Nat.xor (firstAt 5) (LowCycleNormalization.maskAt j)
    let b := betaAt 5
    let t := tag5 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection5 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref5 j, hk⟩
    simpa only [ha, hb, ht] using h
end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFlatData

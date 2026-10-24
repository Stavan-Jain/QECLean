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
theorem selection12 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 12) (LowCycleNormalization.maskAt j)
    let b := betaAt 12
    let t := tag12 j
    let k := DeepFlatBatch.ref12 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 12. -/
theorem checked12 (j : Fin 1954) :
    let a := Nat.xor (firstAt 12) (LowCycleNormalization.maskAt j)
    let b := betaAt 12
    let t := tag12 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection12 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref12 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection13 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 13) (LowCycleNormalization.maskAt j)
    let b := betaAt 13
    let t := tag13 j
    let k := DeepFlatBatch.ref13 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 13. -/
theorem checked13 (j : Fin 1954) :
    let a := Nat.xor (firstAt 13) (LowCycleNormalization.maskAt j)
    let b := betaAt 13
    let t := tag13 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection13 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref13 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection14 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 14) (LowCycleNormalization.maskAt j)
    let b := betaAt 14
    let t := tag14 j
    let k := DeepFlatBatch.ref14 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 14. -/
theorem checked14 (j : Fin 1954) :
    let a := Nat.xor (firstAt 14) (LowCycleNormalization.maskAt j)
    let b := betaAt 14
    let t := tag14 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection14 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref14 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection15 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 15) (LowCycleNormalization.maskAt j)
    let b := betaAt 15
    let t := tag15 j
    let k := DeepFlatBatch.ref15 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 15. -/
theorem checked15 (j : Fin 1954) :
    let a := Nat.xor (firstAt 15) (LowCycleNormalization.maskAt j)
    let b := betaAt 15
    let t := tag15 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection15 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref15 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection16 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 16) (LowCycleNormalization.maskAt j)
    let b := betaAt 16
    let t := tag16 j
    let k := DeepFlatBatch.ref16 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 16. -/
theorem checked16 (j : Fin 1954) :
    let a := Nat.xor (firstAt 16) (LowCycleNormalization.maskAt j)
    let b := betaAt 16
    let t := tag16 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection16 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref16 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection17 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 17) (LowCycleNormalization.maskAt j)
    let b := betaAt 17
    let t := tag17 j
    let k := DeepFlatBatch.ref17 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 17. -/
theorem checked17 (j : Fin 1954) :
    let a := Nat.xor (firstAt 17) (LowCycleNormalization.maskAt j)
    let b := betaAt 17
    let t := tag17 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection17 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref17 j, hk⟩
    simpa only [ha, hb, ht] using h
end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFlatData

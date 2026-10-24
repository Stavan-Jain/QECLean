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
theorem selection6 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 6) (LowCycleNormalization.maskAt j)
    let b := betaAt 6
    let t := tag6 j
    let k := DeepFlatBatch.ref6 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 6. -/
theorem checked6 (j : Fin 1954) :
    let a := Nat.xor (firstAt 6) (LowCycleNormalization.maskAt j)
    let b := betaAt 6
    let t := tag6 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection6 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref6 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection7 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 7) (LowCycleNormalization.maskAt j)
    let b := betaAt 7
    let t := tag7 j
    let k := DeepFlatBatch.ref7 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 7. -/
theorem checked7 (j : Fin 1954) :
    let a := Nat.xor (firstAt 7) (LowCycleNormalization.maskAt j)
    let b := betaAt 7
    let t := tag7 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection7 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref7 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection8 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 8) (LowCycleNormalization.maskAt j)
    let b := betaAt 8
    let t := tag8 j
    let k := DeepFlatBatch.ref8 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 8. -/
theorem checked8 (j : Fin 1954) :
    let a := Nat.xor (firstAt 8) (LowCycleNormalization.maskAt j)
    let b := betaAt 8
    let t := tag8 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection8 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref8 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection9 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 9) (LowCycleNormalization.maskAt j)
    let b := betaAt 9
    let t := tag9 j
    let k := DeepFlatBatch.ref9 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 9. -/
theorem checked9 (j : Fin 1954) :
    let a := Nat.xor (firstAt 9) (LowCycleNormalization.maskAt j)
    let b := betaAt 9
    let t := tag9 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection9 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref9 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection10 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 10) (LowCycleNormalization.maskAt j)
    let b := betaAt 10
    let t := tag10 j
    let k := DeepFlatBatch.ref10 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 10. -/
theorem checked10 (j : Fin 1954) :
    let a := Nat.xor (firstAt 10) (LowCycleNormalization.maskAt j)
    let b := betaAt 10
    let t := tag10 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection10 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref10 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection11 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 11) (LowCycleNormalization.maskAt j)
    let b := betaAt 11
    let t := tag11 j
    let k := DeepFlatBatch.ref11 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 11. -/
theorem checked11 (j : Fin 1954) :
    let a := Nat.xor (firstAt 11) (LowCycleNormalization.maskAt j)
    let b := betaAt 11
    let t := tag11 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection11 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref11 j, hk⟩
    simpa only [ha, hb, ht] using h
end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFlatData

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
theorem selection24 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 24) (LowCycleNormalization.maskAt j)
    let b := betaAt 24
    let t := tag24 j
    let k := DeepFlatBatch.ref24 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 24. -/
theorem checked24 (j : Fin 1954) :
    let a := Nat.xor (firstAt 24) (LowCycleNormalization.maskAt j)
    let b := betaAt 24
    let t := tag24 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection24 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref24 j, hk⟩
    simpa only [ha, hb, ht] using h
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The base census selects either a heavy lift or a verified packed light outcome. -/
theorem selection25 : ∀ j : Fin 1954,
    let a := Nat.xor (firstAt 25) (LowCycleNormalization.maskAt j)
    let b := betaAt 25
    let t := tag25 j
    let k := DeepFlatBatch.ref25 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (k < 2549 ∧ DeepFlatBatch.firstAt k = (if t % 2 = 1 then a ^^^ b else a) ∧
        DeepFlatBatch.betaAt k = b ∧ DeepFlatBatch.indexAt k = t / 2) := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle census accounts for every light lift of deep flat shadow 25. -/
theorem checked25 (j : Fin 1954) :
    let a := Nat.xor (firstAt 25) (LowCycleNormalization.maskAt j)
    let b := betaAt 25
    let t := tag25 j
    22 < fast90 b + 2 * fast90 (Nat.land a (Nat.xor (2^90-1) b)) ∨
      (t / 2 < topBankSize ∧
        bottomJoin (if t % 2 = 1 then a ^^^ b else a) b = topBankMask (t / 2)) := by
  rcases selection25 j with h | ⟨hk, ha, hb, ht⟩
  · exact Or.inl h
  · right
    have h := DeepFlatBatch.result_checked ⟨DeepFlatBatch.ref25 j, hk⟩
    simpa only [ha, hb, ht] using h
end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFlatData

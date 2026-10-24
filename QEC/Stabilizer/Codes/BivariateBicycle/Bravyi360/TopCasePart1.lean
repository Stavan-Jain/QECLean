/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_top_case.py
Data and SHA-256 hashes: root_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCaseCheck

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 10 are kernel-checked. -/
theorem checked10 : (List.range 1024).all (fun j => entryCheck (10240 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 11 are kernel-checked. -/
theorem checked11 : (List.range 1024).all (fun j => entryCheck (11264 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 12 are kernel-checked. -/
theorem checked12 : (List.range 1024).all (fun j => entryCheck (12288 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 13 are kernel-checked. -/
theorem checked13 : (List.range 1024).all (fun j => entryCheck (13312 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 14 are kernel-checked. -/
theorem checked14 : (List.range 1024).all (fun j => entryCheck (14336 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 15 are kernel-checked. -/
theorem checked15 : (List.range 1024).all (fun j => entryCheck (15360 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 16 are kernel-checked. -/
theorem checked16 : (List.range 1024).all (fun j => entryCheck (16384 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 17 are kernel-checked. -/
theorem checked17 : (List.range 1024).all (fun j => entryCheck (17408 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 18 are kernel-checked. -/
theorem checked18 : (List.range 1024).all (fun j => entryCheck (18432 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 19 are kernel-checked. -/
theorem checked19 : (List.range 1024).all (fun j => entryCheck (19456 + j)) = true := by
  decide +kernel
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData

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
/-- The 1024 family associations in bank chunk 20 are kernel-checked. -/
theorem checked20 : (List.range 1024).all (fun j => entryCheck (20480 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 21 are kernel-checked. -/
theorem checked21 : (List.range 1024).all (fun j => entryCheck (21504 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 22 are kernel-checked. -/
theorem checked22 : (List.range 1024).all (fun j => entryCheck (22528 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 23 are kernel-checked. -/
theorem checked23 : (List.range 1024).all (fun j => entryCheck (23552 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 24 are kernel-checked. -/
theorem checked24 : (List.range 1024).all (fun j => entryCheck (24576 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 25 are kernel-checked. -/
theorem checked25 : (List.range 1024).all (fun j => entryCheck (25600 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 26 are kernel-checked. -/
theorem checked26 : (List.range 1024).all (fun j => entryCheck (26624 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 27 are kernel-checked. -/
theorem checked27 : (List.range 1024).all (fun j => entryCheck (27648 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 28 are kernel-checked. -/
theorem checked28 : (List.range 1024).all (fun j => entryCheck (28672 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 29 are kernel-checked. -/
theorem checked29 : (List.range 1024).all (fun j => entryCheck (29696 + j)) = true := by
  decide +kernel
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData

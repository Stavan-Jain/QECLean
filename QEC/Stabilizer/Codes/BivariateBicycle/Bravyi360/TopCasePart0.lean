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
/-- The 1024 family associations in bank chunk 0 are kernel-checked. -/
theorem checked0 : (List.range 1024).all (fun j => entryCheck (0 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 1 are kernel-checked. -/
theorem checked1 : (List.range 1024).all (fun j => entryCheck (1024 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 2 are kernel-checked. -/
theorem checked2 : (List.range 1024).all (fun j => entryCheck (2048 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 3 are kernel-checked. -/
theorem checked3 : (List.range 1024).all (fun j => entryCheck (3072 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 4 are kernel-checked. -/
theorem checked4 : (List.range 1024).all (fun j => entryCheck (4096 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 5 are kernel-checked. -/
theorem checked5 : (List.range 1024).all (fun j => entryCheck (5120 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 6 are kernel-checked. -/
theorem checked6 : (List.range 1024).all (fun j => entryCheck (6144 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 7 are kernel-checked. -/
theorem checked7 : (List.range 1024).all (fun j => entryCheck (7168 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 8 are kernel-checked. -/
theorem checked8 : (List.range 1024).all (fun j => entryCheck (8192 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 9 are kernel-checked. -/
theorem checked9 : (List.range 1024).all (fun j => entryCheck (9216 + j)) = true := by
  decide +kernel
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData

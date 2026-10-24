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
/-- The 1024 family associations in bank chunk 30 are kernel-checked. -/
theorem checked30 : (List.range 1024).all (fun j => entryCheck (30720 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 31 are kernel-checked. -/
theorem checked31 : (List.range 1024).all (fun j => entryCheck (31744 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 32 are kernel-checked. -/
theorem checked32 : (List.range 1024).all (fun j => entryCheck (32768 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 33 are kernel-checked. -/
theorem checked33 : (List.range 1024).all (fun j => entryCheck (33792 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 34 are kernel-checked. -/
theorem checked34 : (List.range 1024).all (fun j => entryCheck (34816 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 35 are kernel-checked. -/
theorem checked35 : (List.range 1024).all (fun j => entryCheck (35840 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 36 are kernel-checked. -/
theorem checked36 : (List.range 1024).all (fun j => entryCheck (36864 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 37 are kernel-checked. -/
theorem checked37 : (List.range 1024).all (fun j => entryCheck (37888 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 38 are kernel-checked. -/
theorem checked38 : (List.range 1024).all (fun j => entryCheck (38912 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 39 are kernel-checked. -/
theorem checked39 : (List.range 1024).all (fun j => entryCheck (39936 + j)) = true := by
  decide +kernel
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData

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
/-- The 1024 family associations in bank chunk 50 are kernel-checked. -/
theorem checked50 : (List.range 1024).all (fun j => entryCheck (51200 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 51 are kernel-checked. -/
theorem checked51 : (List.range 1024).all (fun j => entryCheck (52224 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 52 are kernel-checked. -/
theorem checked52 : (List.range 1024).all (fun j => entryCheck (53248 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 53 are kernel-checked. -/
theorem checked53 : (List.range 1024).all (fun j => entryCheck (54272 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 54 are kernel-checked. -/
theorem checked54 : (List.range 1024).all (fun j => entryCheck (55296 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 1024 family associations in bank chunk 55 are kernel-checked. -/
theorem checked55 : (List.range 1024).all (fun j => entryCheck (56320 + j)) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 786 family associations in bank chunk 56 are kernel-checked. -/
theorem checked56 : (List.range 786).all (fun j => entryCheck (57344 + j)) = true := by
  decide +kernel
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData

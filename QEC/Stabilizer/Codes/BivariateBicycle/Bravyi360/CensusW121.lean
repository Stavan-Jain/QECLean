/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_trellis_censuses.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ConcreteTrellis

noncomputable section

set_option maxRecDepth 1000000

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The affine offset of the W121 census. -/
noncomputable def W121Offset : Nat := 154747230380280876349985376

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The packed exact truncated weight enumerator of the W121 census. -/
noncomputable def W121Answer : Nat := 372380331441014198719368593597035236466279059884417763466559467700847427341906323912835231787249655648933874275202732509334144878032189827424907355617574577033546016706508067333864047676300659927816609682711308211946984406897293762051516798758426233045303347650199089557348206856110080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Kernel evaluation of the entire W121 packed recurrence. -/
theorem W121_computed : (stabSteps W121Offset).foldl (fastPackedStep 42 22) 1 = W121Answer := by decide +kernel
#print axioms W121_computed

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The W121 encoder starts at its specified affine offset. -/
theorem W121_zero : runWord (stabInstructions W121Offset) 0 0 = W121Offset := by decide +kernel
#print axioms W121_zero

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every stored generator is realized by its certified input coefficient. -/
theorem W121_input_checks : stabInputs.all (fun gi => decide (gi.2 < 2 ^ reads (stabInstructions W121Offset)) && decide (runWord (stabInstructions W121Offset) gi.2 0 = gi.1 ^^^ W121Offset)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reducing the packed weight enumerator counts all retained words. -/
theorem W121_answer_count : W121Answer % (2 ^ 42 - 1) = 2949455 := by decide +kernel

#print axioms W121_computed
#print axioms W121_input_checks
end Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

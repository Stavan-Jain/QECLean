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
/-- The affine offset of the cycle census. -/
noncomputable def cycleOffset : Nat := 0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The packed exact truncated weight enumerator of the cycle census. -/
noncomputable def cycleAnswer : Nat := 5951024125155185919683978868832807661218883061479360820006104069934079850436926852973995765612599663302371222418552155802872405752407365206580588684771329

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Kernel evaluation of the entire cycle packed recurrence. -/
theorem cycle_computed : (cycleSteps cycleOffset).foldl (fastPackedStep 50 10) 1 = cycleAnswer := by decide +kernel
#print axioms cycle_computed

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The cycle encoder starts at its specified affine offset. -/
theorem cycle_zero : runWord (cycleInstructions cycleOffset) 0 0 = cycleOffset := by decide +kernel
#print axioms cycle_zero

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every stored generator is realized by its certified input coefficient. -/
theorem cycle_input_checks : cycleInputs.all (fun gi => decide (gi.2 < 2 ^ reads (cycleInstructions cycleOffset)) && decide (runWord (cycleInstructions cycleOffset) gi.2 0 = gi.1 ^^^ cycleOffset)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reducing the packed weight enumerator counts all retained words. -/
theorem cycle_answer_count : cycleAnswer % (2 ^ 50 - 1) = 1954 := by decide +kernel

#print axioms cycle_computed
#print axioms cycle_input_checks
end Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

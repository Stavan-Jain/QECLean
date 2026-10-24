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
/-- The affine offset of the stab census. -/
noncomputable def stabOffset : Nat := 0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The packed exact truncated weight enumerator of the stab census. -/
noncomputable def stabAnswer : Nat := 412371592750707995230928426955691701960553572150968603380992433011998179875871033058716795930546967646648155349676607342671058993965370145002215247849914339749491435056354163635087830635289300920462126157272349870070472255516154607328022533398551258760812212699859115960984982698065921

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Kernel evaluation of the entire stab packed recurrence. -/
theorem stab_computed : (stabSteps stabOffset).foldl (fastPackedStep 42 22) 1 = stabAnswer := by decide +kernel
#print axioms stab_computed

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The stab encoder starts at its specified affine offset. -/
theorem stab_zero : runWord (stabInstructions stabOffset) 0 0 = stabOffset := by decide +kernel
#print axioms stab_zero

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every stored generator is realized by its certified input coefficient. -/
theorem stab_input_checks : stabInputs.all (fun gi => decide (gi.2 < 2 ^ reads (stabInstructions stabOffset)) && decide (runWord (stabInstructions stabOffset) gi.2 0 = gi.1 ^^^ stabOffset)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reducing the packed weight enumerator counts all retained words. -/
theorem stab_answer_count : stabAnswer % (2 ^ 42 - 1) = 3481596 := by decide +kernel

#print axioms stab_computed
#print axioms stab_input_checks
end Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

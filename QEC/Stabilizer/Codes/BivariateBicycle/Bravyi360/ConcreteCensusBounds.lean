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

import QEC.Stabilizer.Framework.Homological.Certificate.TrellisSpanCensus
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Censusstab
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.CensusW121
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.CensusW151
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.CensusW238
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Censuscycle

noncomputable section

set_option maxRecDepth 1000000

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light finite subset of this certified affine span obeys the exact census bound. -/
theorem stab_card_le (target : Finset Nat)
    (hspan : ∀ word ∈ target, XorSpan stabGenerators word)
    (hlight : ∀ word ∈ target, bitCount 90 word ≤ 22) :
    target.card ≤ 3481596 := by
  have h := PackedProgram.card_le_of_span_compute (stabProgram stabOffset 22)
    stabInputs stabOffset target stabAnswer (by decide)
    (by decide) (by decide)
    stab_zero stab_input_checks
    (fun word hw => by simpa only [stabGenerators, stabOffset, Nat.xor_zero] using hspan word hw)
    (fun word hw => by change bitCount 90 word ≤ 22; exact hlight word hw)
    stab_computed (by decide +kernel)
  simpa only [stab_answer_count] using h

#print axioms stab_card_le

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light finite subset of this certified affine span obeys the exact census bound. -/
theorem W121_card_le (target : Finset Nat)
    (hspan : ∀ word ∈ target, XorSpan stabGenerators (word ^^^ W121Offset))
    (hlight : ∀ word ∈ target, bitCount 90 word ≤ 22) :
    target.card ≤ 2949455 := by
  have h := PackedProgram.card_le_of_span_compute (stabProgram W121Offset 22)
    stabInputs W121Offset target W121Answer (by decide)
    (by decide) (by decide)
    W121_zero W121_input_checks
    (fun word hw => by simpa only [stabGenerators, W121Offset, Nat.xor_zero] using hspan word hw)
    (fun word hw => by change bitCount 90 word ≤ 22; exact hlight word hw)
    W121_computed (by decide +kernel)
  simpa only [W121_answer_count] using h

#print axioms W121_card_le

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light finite subset of this certified affine span obeys the exact census bound. -/
theorem W151_card_le (target : Finset Nat)
    (hspan : ∀ word ∈ target, XorSpan stabGenerators (word ^^^ W151Offset))
    (hlight : ∀ word ∈ target, bitCount 90 word ≤ 22) :
    target.card ≤ 2949455 := by
  have h := PackedProgram.card_le_of_span_compute (stabProgram W151Offset 22)
    stabInputs W151Offset target W151Answer (by decide)
    (by decide) (by decide)
    W151_zero W151_input_checks
    (fun word hw => by simpa only [stabGenerators, W151Offset, Nat.xor_zero] using hspan word hw)
    (fun word hw => by change bitCount 90 word ≤ 22; exact hlight word hw)
    W151_computed (by decide +kernel)
  simpa only [W151_answer_count] using h

#print axioms W151_card_le

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light finite subset of this certified affine span obeys the exact census bound. -/
theorem W238_card_le (target : Finset Nat)
    (hspan : ∀ word ∈ target, XorSpan stabGenerators (word ^^^ W238Offset))
    (hlight : ∀ word ∈ target, bitCount 90 word ≤ 22) :
    target.card ≤ 2949455 := by
  have h := PackedProgram.card_le_of_span_compute (stabProgram W238Offset 22)
    stabInputs W238Offset target W238Answer (by decide)
    (by decide) (by decide)
    W238_zero W238_input_checks
    (fun word hw => by simpa only [stabGenerators, W238Offset, Nat.xor_zero] using hspan word hw)
    (fun word hw => by change bitCount 90 word ≤ 22; exact hlight word hw)
    W238_computed (by decide +kernel)
  simpa only [W238_answer_count] using h

#print axioms W238_card_le

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light finite subset of this certified affine span obeys the exact census bound. -/
theorem cycle_card_le (target : Finset Nat)
    (hspan : ∀ word ∈ target, XorSpan cycleGenerators word)
    (hlight : ∀ word ∈ target, bitCount 90 word ≤ 10) :
    target.card ≤ 1954 := by
  have h := PackedProgram.card_le_of_span_compute (cycleProgram cycleOffset 10)
    cycleInputs cycleOffset target cycleAnswer (by decide)
    (by decide) (by decide)
    cycle_zero cycle_input_checks
    (fun word hw => by simpa only [cycleGenerators, cycleOffset, Nat.xor_zero] using hspan word hw)
    (fun word hw => by change bitCount 90 word ≤ 10; exact hlight word hw)
    cycle_computed (by decide +kernel)
  simpa only [cycle_answer_count] using h

#print axioms cycle_card_le

end Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

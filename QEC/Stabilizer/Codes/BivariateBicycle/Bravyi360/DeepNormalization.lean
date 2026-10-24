/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_deep_normalization.py
Data and SHA-256 hashes: root_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomCaseData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepFiberData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TranslationNormalization

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.DeepNormalization
open F2Mask
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed indexAt choices for the deep representative normalization. -/
noncomputable def indexAt (i : Nat) : Nat := (0xce2f6316b49937a944707b9ac5a92811c20 >>> (5 * i)) % 2 ^ 5
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed xAt choices for the deep representative normalization. -/
noncomputable def xAt (i : Nat) : Nat := (0x44444daa43abbb0000003000900 >>> (4 * i)) % 2 ^ 4
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed yAt choices for the deep representative normalization. -/
noncomputable def yAt (i : Nat) : Nat := (0xaaa2a1a861a182 >>> (2 * i)) % 2 ^ 2
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Translate a canonical deep representative to the checked affine representative. -/
noncomputable def displacement (i : Nat) : BaseGroup := (xAt i, yAt i)
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each deep representative has a checked translation into the affine certificate order. -/
theorem checked : ∀ i : Fin 28, indexAt i < 28 ∧
    maskOf baseQubitEnum (translate1 (displacement i)
      (chainOfMask baseQubitEnum (BottomCase.deepBeta i))) = DeepFiberData.betaAt (indexAt i) := by
  decide +kernel
end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepNormalization

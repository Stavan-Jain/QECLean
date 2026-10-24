/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_affine_search.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Framework.Homological.Certificate.SearchCertificate
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Adjoints

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.F2Mask.AffineSearchData
open PackedDigits BB.Bravyi360 BB.Bravyi360.FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The top transpose fits in all256-bit search lanes. -/
theorem topTranspose_bounded : ∀ p ∈ topETransposeColumns, p.1 < 256 ∧ p.2 < 2^256 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The bottom transpose fits in all256-bit search lanes. -/
theorem bottomTranspose_bounded : ∀ p ∈ bottomETransposeColumns, p.1 < 256 ∧ p.2 < 2^256 := by decide +kernel

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

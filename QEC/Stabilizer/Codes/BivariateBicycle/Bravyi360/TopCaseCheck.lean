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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopCaseData

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A direct Boolean version of the family-association predicate. -/
noncomputable def entryCheck (i : Nat) : Bool :=
  let family := tagAt i % 8
  let j := tagAt i / 8
  let beta := topBankMask i
  Nat.blt family 6 && Nat.blt j (familySize family) &&
    Nat.beq beta (familyBeta family j) &&
    (Nat.blt family 2 || Nat.ble ((22 - fast180 beta) / 2) (familyCap family))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Boolean family validation implies the mathematical family predicate. -/
theorem entryCheck_sound (i : Nat) (h : entryCheck i = true) : Valid i := by
  simp only [entryCheck, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq,
    Nat.ble_eq, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, fun hf => h.2.resolve_left (by omega)⟩
end Quantum.Stabilizer.Homological.BB.Bravyi360.TopCaseData

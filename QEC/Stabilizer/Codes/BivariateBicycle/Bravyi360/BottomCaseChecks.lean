/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_bottom_case.py
Data and SHA-256 hashes: root_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomCaseData

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomCase
set_option maxRecDepth 200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The sparse deep positions contain their stated canonical shadows. -/
theorem deep_sparse_checked : ∀ j : Fin 28,
    OrbitBatchData.repAt (deepOrbitIndex j) = deepBeta j := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every guarded deep tag points to its actual deep shadow. -/
theorem deep_checked (i : Fin 274011) (hd : tag i = 5) :
    localIndex i < 28 ∧ OrbitBatchData.repAt i = deepBeta (localIndex i) := by
  have hg : localIndex i < 28 ∧ i.val = deepOrbitIndex (localIndex i) := by
    unfold tag at hd
    split_ifs at hd with hraw hguard
    · exact hguard
    · contradiction
    · have hm := Nat.min_le_right (entry i % 8) 4
      omega
  refine ⟨hg.1, ?_⟩
  exact (congrArg OrbitBatchData.repAt hg.2).trans
    (deep_sparse_checked ⟨localIndex i, hg.1⟩)
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomCase

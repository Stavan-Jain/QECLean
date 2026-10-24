/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/mark_research_noncomputable.py
Data and SHA-256 hashes: research_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitBatchMetadataChecks

noncomputable section

namespace OrbitBatchData

/-- Orbit-stabilizer counts sum to the independently counted reachable population. -/
theorem orbit_size_sum : (∑ i : Fin 274011, 45/fixedAt i.val) = 12329961 := by
  have he := exceptional_counts
  have hsum := Quantum.Stabilizer.Homological.sum_of_exceptional_values
    (fun i : Fin 274011 => 45/fixedAt i.val) exceptional 45 274011 17 231
    (Fintype.card_fin 274011) he.1 he.2
    (fun i hi => by change 45 / fixedAt i.val = 45; rw [fixedAt_of_not_exceptional i hi])
  exact hsum.trans (by decide +kernel)

end OrbitBatchData

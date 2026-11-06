/-
# The weight-10 distance witness of the `[[150,30,10]]` mitten code

The generated `witSup` (weight 10,
`∈ ker H_X`) is a dual cycle of `m150Complex` that is **not** a dual
boundary, certified by the explicit pairing chain `witPairSup`
(`∈ ker H_Z`, inner product `1`). The transpose identity makes this
pairing vanish on every dual boundary.

Headline (`m150_exists_weight10_nontrivial_dualCycle`): the mitten
complex has a weight-10 nontrivial Z-logical chain — the kernel-checked
`d ≤ 10` half of the distance. The two floor modules supply the lower
bound. Provenance:
`qec-lab:experiments/bb_lab/scripts/m150_gen_lean_data.py` (witness
validated in numpy before emission; SAT ground truth
`qec-lab:experiments/bb_lab/certificates/mitten_150_30_10_{X,Z}.cert.json`).
-/

import QEC.Stabilizer.Codes.Mitten.M150.SparseSupport

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators

/-- The weight-10 witness 1-chain (indicator of `witSup`). -/
def witChain : Fin 5 × M150G → ZMod 2 :=
  supportChain witSup

/-- Its dual pairing 1-chain (indicator of `witPairSup`, weight 18). -/
def witPairChain : Fin 5 × M150G → ZMod 2 :=
  supportChain witPairSup

/-- The witness satisfies every dual check, computed only on its ten entries. -/
private lemma wit_syndrome : ∀ p : Fin 2 × M150G,
    (∑ q ∈ (witSup.map qubitOf).toFinset, d2term p q) = 0 := by
  decide +kernel

/-- The separating chain satisfies every primal check. -/
private lemma pair_syndrome : ∀ p : Fin 2 × M150G,
    (∑ q ∈ (witPairSup.map qubitOf).toFinset, cmTerm p q) = 0 := by
  decide +kernel

/-- The witness is a dual cycle. -/
theorem witChain_dualBoundary : m150Complex.dualBoundary witChain = 0 := by
  funext p
  exact (dualBoundary_supportChain witSup p).trans (wit_syndrome p)

/-- The pairing chain is a cycle. -/
theorem witPairChain_boundary1 : m150Complex.boundary1 witPairChain = 0 := by
  funext p
  exact (boundary1_supportChain witPairSup p).trans (pair_syndrome p)

/-- The two certified chains have odd intersection. -/
theorem witPair_pairing :
    ∑ e : Fin 5 × M150G, witPairChain e * witChain e = 1 := by
  rw [witPairChain, supportChain_pairing]
  decide +kernel

/-- The witness has chain weight exactly ten. -/
theorem chainWeight_witChain : m150Complex.chainWeight witChain = 10 := by
  change (Finset.univ.filter fun q : Fin 5 × M150G => witChain q ≠ 0).card = 10
  decide +kernel

/-- The witness is not a dual boundary (dual-witness certificate). -/
theorem witChain_not_mem_dualBoundaries :
    witChain ∉ m150Complex.dualBoundaries := by
  rintro ⟨s, hs⟩
  have h0 : ∑ e : m150Complex.C1, witPairChain e * m150Complex.cutMap s e = 0 := by
    rw [← m150Complex.boundary1_cutMap_transpose witPairChain s, witPairChain_boundary1]
    simp
  rw [hs] at h0
  exact one_ne_zero (witPair_pairing.symm.trans h0)

/-- **The `[[150,30,10]]` mitten complex has a weight-10 nontrivial
Z-logical chain** — the kernel-checked upper bound on the distance. -/
theorem m150_exists_weight10_nontrivial_dualCycle :
    ∃ v ∈ m150Complex.dualCycles,
      v ∉ m150Complex.dualBoundaries ∧ m150Complex.chainWeight v = 10 :=
  ⟨witChain, LinearMap.mem_ker.mpr witChain_dualBoundary,
    witChain_not_mem_dualBoundaries, chainWeight_witChain⟩

end M150
end LP
end Homological
end Stabilizer
end Quantum

#print axioms Quantum.Stabilizer.Homological.LP.M150.m150_exists_weight10_nontrivial_dualCycle

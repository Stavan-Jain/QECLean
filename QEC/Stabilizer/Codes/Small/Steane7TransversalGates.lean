import QEC.Stabilizer.Codes.Small.Steane7Logicals
import QEC.Stabilizer.Foundations.PauliGroup.TransversalConjugation
import QEC.Stabilizer.Framework.Core.Logical.LogicalCliffordAction
import QEC.Stabilizer.Framework.Core.Logical.LogicalGates

/-!
# Transversal `H` and `S` on the Steane code

The uniform transversal Hadamard gate `H⊗⁷` and the uniform transversal inverse
phase gate `(S†)⊗⁷` are logical gates of the Steane code, and they act on the
logical basis `X̄ = X⊗⁷`, `Z̄ = Z⊗⁷` of `Steane7.stabilizerCodeWithLogicals` as
the logical Hadamard and the logical phase gate.

Conjugation by a gate `U` means `P ↦ U P U†`. A gate whose conjugation maps
every generator into the stabilizer group is a logical gate
(`isLogicalGate_of_generator_set_conjugation`):

- `H⊗⁷` exchanges `X` and `Z` on every qubit, so it exchanges the Z-check and
  the X-check on each Hamming row, and it exchanges `X̄` and `Z̄`.
- `(S†)⊗⁷` fixes `Z` and sends `X` to `−Y` on every qubit. It fixes each Z-check
  and `Z̄`. An X-check has weight four, so it goes to `Y` on its row, the
  product of the X-check and the Z-check on that row. `X̄` has weight seven, so
  it goes to `−Y⊗⁷ = i X̄ Z̄`, the logical `Y`.

## Outline

- The gates `transversalH`, `transversalS`
- Conjugation of Pauli group elements: `conjByGate_transversalH`,
  `conjByGate_transversalS_of_Z`, `conjByGate_transversalS_of_X`
- `transversalH_isLogicalGate`, `transversalH_isLogicalHadamard`
- `transversalS_isLogicalGate`, `transversalS_isLogicalS`
-/

namespace Quantum
namespace StabilizerGroup
namespace Steane7

open NQubitPauliGroupElement

/-! ## The transversal gates -/

/-- Transversal Hadamard: `H` on each of the seven physical qubits. -/
noncomputable def transversalH : NQubitGate 7 :=
  uniformTransversalGate 7 H

/-- Transversal inverse phase gate: `S†` on each of the seven physical qubits.
Its conjugation action is the logical phase gate `S`
(`transversalS_isLogicalS`). -/
noncomputable def transversalS : NQubitGate 7 :=
  uniformTransversalGate 7 inv_S

/-! ## Transversal `H` -/

/-- The Pauli group element with `X` and `Z` exchanged on every qubit, and the
same phase. -/
def swapXZ (g : NQubitPauliGroupElement 7) : NQubitPauliGroupElement 7 :=
  ⟨g.phasePower, g.operators.transversalSwapXZ⟩

/-- Transversal `H` conjugates a Pauli group element with no `Y` factor to the
element with `X` and `Z` exchanged. -/
lemma conjByGate_transversalH (g : NQubitPauliGroupElement 7)
    (hg : ∀ i, g.operators i ≠ .Y) :
    conjByGate transversalH g.gate = (swapXZ g).gate := by
  rw [conjByGate_gate_eq_iff]
  change uniformTransversalGateMatrix 7 H * g.toMatrix *
    star (uniformTransversalGateMatrix 7 H) = (swapXZ g).toMatrix
  simp only [NQubitPauliGroupElement.toMatrix, Matrix.mul_smul, Matrix.smul_mul,
    uniformTransversalGateMatrix_H_conj_op 7 g.operators hg, swapXZ]

/-- Transversal Hadamard is a logical gate of the Steane code: it exchanges the
Z-check and the X-check on each Hamming row. -/
theorem transversalH_isLogicalGate : IsLogicalGate transversalH stabilizerGroup := by
  refine isLogicalGate_of_generator_set_conjugation _ _ _ stabilizerGroup_toSubgroup_eq
    fun g (hg : g ∈ generatorsList) => ⟨swapXZ g,
      Subgroup.subset_closure (?_ : swapXZ g ∈ generatorsList), conjByGate_transversalH g ?_⟩
  all_goals fin_cases hg <;> decide

/-- Transversal Hadamard acts as the logical Hadamard on the logical basis of
`stabilizerCodeWithLogicals`: it conjugates `X̄` to `Z̄` and `Z̄` to `X̄`. -/
theorem transversalH_isLogicalHadamard :
    LogicalQubitOps.IsLogicalHadamard (stabilizerCodeWithLogicals.logicalOps 0) transversalH :=
  ⟨transversalH_isLogicalGate, conjByGate_transversalH logicalX (by decide),
    conjByGate_transversalH logicalZ (by decide)⟩

/-! ## Transversal `S` -/

/-- Transversal `S†` fixes a Pauli group element whose factors are all `Z` or
`I`. -/
lemma conjByGate_transversalS_of_Z (g : NQubitPauliGroupElement 7)
    (hg : ∀ i, g.operators i = .Z ∨ g.operators i = .I) :
    conjByGate transversalS g.gate = g.gate := by
  rw [conjByGate_gate_eq_iff]
  change uniformTransversalGateMatrix 7 inv_S * g.toMatrix *
    star (uniformTransversalGateMatrix 7 inv_S) = g.toMatrix
  simp only [NQubitPauliGroupElement.toMatrix, Matrix.mul_smul, Matrix.smul_mul,
    uniformTransversalGateMatrix_inv_S_conj_Z_op 7 g.operators hg]

/-- Transversal `S†` conjugates a phase-0 Pauli group element `g` whose factors
are all `X` or `I` to `h`, where `h` is `Y` on the `X`-support of `g` with the
sign `(-1) ^ |X-support|`: phase power `0` if the support is even, `2` if it is
odd. -/
lemma conjByGate_transversalS_of_X {g h : NQubitPauliGroupElement 7}
    (hphase : g.phasePower = 0) (hg : ∀ i, g.operators i = .X ∨ g.operators i = .I)
    (hh : h = ⟨if Even (xSupport g.operators).card then 0 else 2,
      invSConjXIImage g.operators⟩) :
    conjByGate transversalS g.gate = h.gate := by
  rw [conjByGate_gate_eq_iff, hh]
  refine (uniformTransversalGateMatrix_inv_S_conj_element_XI_phase0 7 g hphase hg).trans ?_
  rw [invSConjXIScalar_eq_negOne_pow_xSupportCard]
  split_ifs with hc
  · simp [NQubitPauliGroupElement.toMatrix, hc.neg_one_pow]
  · simp [NQubitPauliGroupElement.toMatrix, (Nat.not_even_iff_odd.mp hc).neg_one_pow]

/-- Transversal `S†` is a logical gate of the Steane code: it fixes each
Z-check and sends the X-check on a Hamming row to its product with the Z-check
on that row. -/
theorem transversalS_isLogicalGate : IsLogicalGate transversalS stabilizerGroup := by
  have hmem : ∀ g ∈ generatorsList, g ∈ stabilizerGroup.toSubgroup :=
    fun g hg => Subgroup.subset_closure hg
  refine isLogicalGate_of_generator_set_conjugation _ _ _ stabilizerGroup_toSubgroup_eq
    fun g (hg : g ∈ generatorsList) => ?_
  fin_cases hg
  · exact ⟨Z1, hmem _ (by decide), conjByGate_transversalS_of_Z _ (by decide)⟩
  · exact ⟨Z2, hmem _ (by decide), conjByGate_transversalS_of_Z _ (by decide)⟩
  · exact ⟨Z3, hmem _ (by decide), conjByGate_transversalS_of_Z _ (by decide)⟩
  · exact ⟨X1 * Z1, Subgroup.mul_mem _ (hmem X1 (by decide)) (hmem Z1 (by decide)),
      conjByGate_transversalS_of_X rfl (by decide) (by decide)⟩
  · exact ⟨X2 * Z2, Subgroup.mul_mem _ (hmem X2 (by decide)) (hmem Z2 (by decide)),
      conjByGate_transversalS_of_X rfl (by decide) (by decide)⟩
  · exact ⟨X3 * Z3, Subgroup.mul_mem _ (hmem X3 (by decide)) (hmem Z3 (by decide)),
      conjByGate_transversalS_of_X rfl (by decide) (by decide)⟩

/-- Transversal `S†` acts as the logical phase gate `S` on the logical basis of
`stabilizerCodeWithLogicals`: it fixes `Z̄` and conjugates `X̄` to
`Ȳ = i X̄ Z̄`. -/
theorem transversalS_isLogicalS :
    LogicalQubitOps.IsLogicalS (stabilizerCodeWithLogicals.logicalOps 0) transversalS :=
  ⟨transversalS_isLogicalGate, conjByGate_transversalS_of_Z logicalZ (by decide),
    conjByGate_transversalS_of_X rfl (by decide) (by decide)⟩

end Steane7
end StabilizerGroup
end Quantum

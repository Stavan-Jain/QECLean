import QEC.Stabilizer.Codes.Small.Shor9

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace Shor9

/-!
# Shor's code `[[9, 1, 3]]`: logical operators

The logical basis of `Shor9.stabilizerCode` in Shor's codeword basis.
Shor encodes `|0⟩ ↦ (|000⟩ + |111⟩)^⊗3 / 2√2` and
`|1⟩ ↦ (|000⟩ − |111⟩)^⊗3 / 2√2`. `Z⊗⁹` flips the sign of `|111⟩` in every
block, swapping the two codewords, so it is the logical `X`; `X⊗⁹` fixes `|0̄⟩`
and multiplies `|1̄⟩` by `(−1)³`, so it is the logical `Z`. These roles are the
reverse of the Steane code's. Both commute with every check (a `Z`-check meets
`X⊗⁹`, and an `X`-check meets `Z⊗⁹`, on an even number of qubits) and they
anticommute, overlapping on nine qubits.

## Outline

- Logical operators `logicalX = Z⊗⁹`, `logicalZ = X⊗⁹`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[9, 1]]ₗ`
-/

open NQubitPauliGroupElement

/-! ## Logical operators -/

/-- Logical X: Z on all nine qubits. -/
def logicalX : NQubitPauliGroupElement 9 :=
  ⟨0, NQubitPauliOperator.Z 9⟩

/-- Logical Z: X on all nine qubits. -/
def logicalZ : NQubitPauliGroupElement 9 :=
  ⟨0, NQubitPauliOperator.X 9⟩

/-! ## Anticommutation -/

/-- `X̄ = Z⊗⁹` and `Z̄ = X⊗⁹` anticommute: they meet on all nine qubits, an odd
number. -/
theorem logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the eight generators, a
closed conjunction that `decide` settles. -/

/-- `X̄ = Z⊗⁹` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `Z̄ = X⊗⁹` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-! ## The code with its logical basis `Code[[9, 1]]ₗ` -/

/-- The single logical qubit `(X̄, Z̄)`. -/
private def logicalOpsShor9 : Fin 1 → LogicalQubitOps 9 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩

/-- Shor's code with its logical basis `X̄ = Z⊗⁹`, `Z̄ = X⊗⁹`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[9, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOpsShor9
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end Shor9
end StabilizerGroup

end Quantum

import QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace FiveQubit_5_1_3

/-!
# The five-qubit perfect code `[[5, 1, 3]]`: logical operators

The standard logical basis of `FiveQubit_5_1_3.stabilizerCode` (Gottesman / EC
Zoo convention): transversal `X̄ = X⊗⁵` and `Z̄ = Z⊗⁵`. Each meets every
generator in exactly two non-identity clashes, so both commute with the
stabilizer, and they anticommute with each other (five qubits, an odd number).

## Outline

- Logical operators `logicalX`, `logicalZ` (and `logicalY = i X̄ Z̄`)
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[5, 1]]ₗ`
-/

open NQubitPauliGroupElement

/-! ## Logical operators -/

/-- Logical X: X on all five qubits. -/
def logicalX : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.X 5⟩

/-- Logical Z: Z on all five qubits. -/
def logicalZ : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.Z 5⟩

/-- Logical Y with the convention `Ȳ = i X̄ Z̄`. -/
noncomputable def logicalY : NQubitPauliGroupElement 5 :=
  NQubitPauliGroupElement.phaseI 5 * (logicalX * logicalZ)

/-! ## Anticommutation -/

/-- `X̄` and `Z̄` anticommute: they meet on all five qubits, an odd number. -/
theorem logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the four generators, a
closed conjunction that `decide` settles. -/

/-- `X̄` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `Z̄` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-! ## The code with its logical basis `Code[[5, 1]]ₗ` -/

/-- The single logical qubit `(X̄, Z̄)`. -/
private def logicalOps5_1_3 : Fin 1 → LogicalQubitOps 5 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩

/-- The five-qubit perfect code with its logical basis `X̄ = X⊗⁵`,
`Z̄ = Z⊗⁵`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[5, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOps5_1_3
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end FiveQubit_5_1_3
end StabilizerGroup

end Quantum

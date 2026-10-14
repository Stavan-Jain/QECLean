import QEC.Stabilizer.Codes.Repetition.Three
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace RepetitionCode3

/-!
# The 3-qubit repetition code `[[3, 1, 1]]`: logical operators

The logical basis of `RepetitionCode3.stabilizerCode`: transversal
`X̄ = XXX` and `Z̄ = ZZZ`. `X̄` meets each `ZZ` check on two qubits and `Z̄` is
Z-type, so both commute with the stabilizer; they anticommute with each other
(three qubits, an odd number).

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[3, 1]]ₗ`
-/

open NQubitPauliGroupElement

/-! ## Logical operators -/

/-- Logical X: X on all three qubits. -/
def logicalX : NQubitPauliGroupElement 3 :=
  ⟨0, NQubitPauliOperator.X 3⟩

/-- Logical Z: Z on all three qubits. -/
def logicalZ : NQubitPauliGroupElement 3 :=
  ⟨0, NQubitPauliOperator.Z 3⟩

/-- Logical X is X-type (X on every qubit). -/
lemma logicalX_is_XType : IsXTypeElement logicalX := by
  constructor
  · rfl
  · intro i
    fin_cases i <;> simp [logicalX, NQubitPauliOperator.X, PauliOperator.IsXType]

/-! ## Anticommutation -/

/-- `X̄` and `Z̄` anticommute: they meet on all three qubits, an odd number. -/
theorem logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the two generators, a
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

/-! ## The code with its logical basis `Code[[3, 1]]ₗ` -/

/-- The single logical qubit `(X̄, Z̄)`. -/
private def logicalOpsRep3 : Fin 1 → LogicalQubitOps 3 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩

/-- The 3-qubit repetition code with its logical basis `X̄ = XXX`,
`Z̄ = ZZZ`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[3, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOpsRep3
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end RepetitionCode3
end StabilizerGroup

end Quantum

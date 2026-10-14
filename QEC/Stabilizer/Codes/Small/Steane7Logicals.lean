import QEC.Stabilizer.Codes.Small.Steane7

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace Steane7

/-!
# The Steane code `[[7, 1, 3]]`: logical operators

The canonical logical basis of `Steane7.stabilizerCode`: transversal
`X̄ = X⊗⁷` and `Z̄ = Z⊗⁷`. Both commute with every check (each row has even
weight four) and they anticommute with each other (seven qubits, an odd
number).

## Outline

- Logical operators `logicalX`, `logicalZ` (and `logicalY = i X̄ Z̄`)
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[7, 1]]ₗ`
-/

open NQubitPauliGroupElement

/-! ## Logical operators -/

/-- Logical X: X on all seven qubits. -/
def logicalX : NQubitPauliGroupElement 7 :=
  ⟨0, NQubitPauliOperator.X 7⟩

/-- Logical Z: Z on all seven qubits. -/
def logicalZ : NQubitPauliGroupElement 7 :=
  ⟨0, NQubitPauliOperator.Z 7⟩

/-- Logical Y with the convention `Ȳ = i X̄ Z̄`. -/
noncomputable def logicalY : NQubitPauliGroupElement 7 :=
  NQubitPauliGroupElement.phaseI 7 * (logicalX * logicalZ)

/-- Steane logical `Ȳ` is phase-2 all-`Y`, under the convention `Ȳ = i X̄ Z̄`.
-/
lemma logicalY_eq_phase2_allY :
    logicalY = ({ phasePower := (2 : Fin 4), operators := NQubitPauliOperator.Y 7 } :
      NQubitPauliGroupElement 7) := by
  decide

/-! ## Anticommutation -/

/-- `X̄` and `Z̄` anticommute: they meet on all seven qubits, an odd number. -/
theorem logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the six generators, a
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

/-! ## The code with its logical basis `Code[[7, 1]]ₗ` -/

/-- The single logical qubit `(X̄, Z̄)`. -/
private def logicalOpsSteane7 : Fin 1 → LogicalQubitOps 7 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩

/-- The Steane code with its logical basis `X̄ = X⊗⁷`, `Z̄ = Z⊗⁷`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[7, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOpsSteane7
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end Steane7
end StabilizerGroup

end Quantum

import QEC.Stabilizer.Codes.Repetition.Three

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

namespace Quantum
namespace StabilizerGroup
namespace RepetitionCode3

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- Logical X: X on all three qubits. -/
def logicalX : NQubitPauliGroupElement 3 :=
  ⟨0, NQubitPauliOperator.X 3⟩

/-- Logical Z: Z on all three qubits. -/
def logicalZ : NQubitPauliGroupElement 3 :=
  ⟨0, NQubitPauliOperator.Z 3⟩

/-! ## Anticommutation -/

/-- `X̄ = XXX` and `Z̄ = ZZZ` anticommute: they meet on all three qubits, an odd
number. -/
lemma logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the two generators, a
closed statement that `decide` settles. -/

/-- `X̄ = XXX` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄ = ZZZ` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-! ## The code with its logical basis `Code[[3, 1]]ₗ` -/

/-- The 3-qubit repetition code with its logical basis `X̄ = XXX`,
`Z̄ = ZZZ`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[3, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps _ := ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩
  logical_commute_cross ℓ ℓ' h := (h (Subsingleton.elim ℓ ℓ')).elim

end RepetitionCode3
end StabilizerGroup
end Quantum

import QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3

/-!
# The five-qubit code `[[5, 1, 3]]`: logical operators

The standard logical basis of `FiveQubit_5_1_3.stabilizerCode`: transversal
`X̄ = X⊗⁵` and `Z̄ = Z⊗⁵`. Each meets every generator in exactly two
non-identity clashes, so both commute with the stabilizer, and they anticommute
with each other (five qubits, an odd number).

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[5, 1]]ₗ`
-/

namespace Quantum
namespace StabilizerGroup
namespace FiveQubit_5_1_3

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- Logical X: X on all five qubits. -/
def logicalX : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.X 5⟩

/-- Logical Z: Z on all five qubits. -/
def logicalZ : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.Z 5⟩

/-! ## Anticommutation -/

/-- `X̄ = X⊗⁵` and `Z̄ = Z⊗⁵` anticommute: they meet on all five qubits, an odd
number. -/
lemma logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the four generators, a
closed statement that `decide` settles. -/

/-- `X̄ = X⊗⁵` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄ = Z⊗⁵` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-! ## The code with its logical basis `Code[[5, 1]]ₗ` -/

/-- The five-qubit code with its logical basis `X̄ = X⊗⁵`, `Z̄ = Z⊗⁵`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[5, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps _ := ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩
  logical_commute_cross ℓ ℓ' h := (h (Subsingleton.elim ℓ ℓ')).elim

end FiveQubit_5_1_3
end StabilizerGroup
end Quantum

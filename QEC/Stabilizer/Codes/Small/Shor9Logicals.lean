import QEC.Stabilizer.Codes.Small.Shor9

/-!
# Shor's code `[[9, 1, 3]]`: logical operators

The logical basis of `Shor9.stabilizerCode` in Shor's codeword basis
```
|0_L⟩ = (|000⟩ + |111⟩)^⊗3 / 2√2,   |1_L⟩ = (|000⟩ − |111⟩)^⊗3 / 2√2
```
`Z⊗⁹` flips the sign of `|111⟩` in every block, swapping the two codewords, so
it is the logical `X`; `X⊗⁹` fixes `|0_L⟩` and multiplies `|1_L⟩` by `(−1)³`,
so it is the logical `Z`. These roles are the reverse of the Steane code's.
Both commute with every check (a Z-check meets `X⊗⁹`, and an X-check meets
`Z⊗⁹`, on an even number of qubits) and they anticommute with each other (nine
qubits, an odd number).

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[9, 1]]ₗ`
-/

namespace Quantum
namespace StabilizerGroup
namespace Shor9

open NQubitPauliGroupElement
open scoped Pauli

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
lemma logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the eight generators, a
closed statement that `decide` settles. -/

/-- `X̄ = Z⊗⁹` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄ = X⊗⁹` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-! ## The code with its logical basis `Code[[9, 1]]ₗ` -/

/-- Shor's code with its logical basis `X̄ = Z⊗⁹`, `Z̄ = X⊗⁹`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[9, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps _ := ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩
  logical_commute_cross ℓ ℓ' h := (h (Subsingleton.elim ℓ ℓ')).elim

end Shor9
end StabilizerGroup
end Quantum

import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2

/-!
# The four-qubit code `[[4, 2, 2]]`: logical operators

The logical basis of `FourQubit_4_2_2.stabilizerCode` matching the codeword
basis
```
|0̄0̄⟩ = (|0000⟩ + |1111⟩)/√2
|0̄1̄⟩ = (|0011⟩ + |1100⟩)/√2
|1̄0̄⟩ = (|0101⟩ + |1010⟩)/√2
|1̄1̄⟩ = (|0110⟩ + |1001⟩)/√2
```
namely
```
X̄₁ = IXIX,  X̄₂ = IIXX,  Z̄₁ = IIZZ,  Z̄₂ = IZIZ.
```
Each `X̄ℓ` anticommutes with its own `Z̄ℓ` (one shared qubit) and commutes with
the other logical qubit's operators (two shared qubits, or the same type).

## Outline

- Logical operators `logicalX_1`, `logicalX_2`, `logicalZ_1`, `logicalZ_2`
- Anticommutation `logicalX_1_anticommutes_logicalZ_1`,
  `logicalX_2_anticommutes_logicalZ_2`
- Centralizer membership `logicalX_ℓ_mem_centralizer`,
  `logicalZ_ℓ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[4, 2]]ₗ`
-/

namespace Quantum
namespace StabilizerGroup
namespace FourQubit_4_2_2

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- Logical X for logical qubit 1: `IXIX`. -/
def logicalX_1 : NQubitPauliGroupElement 4 := σ[IXIX]

/-- Logical X for logical qubit 2: `IIXX`. -/
def logicalX_2 : NQubitPauliGroupElement 4 := σ[IIXX]

/-- Logical Z for logical qubit 1: `IIZZ`. -/
def logicalZ_1 : NQubitPauliGroupElement 4 := σ[IIZZ]

/-- Logical Z for logical qubit 2: `IZIZ`. -/
def logicalZ_2 : NQubitPauliGroupElement 4 := σ[IZIZ]

/-! ## Anticommutation -/

/-- `X̄₁ = IXIX` and `Z̄₁ = IIZZ` anticommute: they meet on qubit 3 only. -/
lemma logicalX_1_anticommutes_logicalZ_1 : Anticommute logicalX_1 logicalZ_1 := by
  decide

/-- `X̄₂ = IIXX` and `Z̄₂ = IZIZ` anticommute: they meet on qubit 3 only. -/
lemma logicalX_2_anticommutes_logicalZ_2 : Anticommute logicalX_2 logicalZ_2 := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the two generators, a
closed statement that `decide` settles. -/

/-- `X̄₁ = IXIX` commutes with every element of the stabilizer. -/
lemma logicalX_1_mem_centralizer : logicalX_1 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `X̄₂ = IIXX` commutes with every element of the stabilizer. -/
lemma logicalX_2_mem_centralizer : logicalX_2 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄₁ = IIZZ` commutes with every element of the stabilizer. -/
lemma logicalZ_1_mem_centralizer : logicalZ_1 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄₂ = IZIZ` commutes with every element of the stabilizer. -/
lemma logicalZ_2_mem_centralizer : logicalZ_2 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-! ## The code with its logical basis `Code[[4, 2]]ₗ` -/

/-- The `[[4, 2, 2]]` code with its logical basis `(X̄₁, Z̄₁)`, `(X̄₂, Z̄₂)`.
The operators of distinct logical qubits commute: `X̄₁` and `Z̄₂` meet on qubits
1 and 3, `X̄₂` and `Z̄₁` on qubits 2 and 3, and the others have the same
type. -/
noncomputable def stabilizerCodeWithLogicals : Code[[4, 2]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps
    | 0 => ⟨logicalX_1, logicalZ_1, logicalX_1_mem_centralizer, logicalZ_1_mem_centralizer,
        logicalX_1_anticommutes_logicalZ_1⟩
    | 1 => ⟨logicalX_2, logicalZ_2, logicalX_2_mem_centralizer, logicalZ_2_mem_centralizer,
        logicalX_2_anticommutes_logicalZ_2⟩
  logical_commute_cross := by decide

end FourQubit_4_2_2
end StabilizerGroup
end Quantum

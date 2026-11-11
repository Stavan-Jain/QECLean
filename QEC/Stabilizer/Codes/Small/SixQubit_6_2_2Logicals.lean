import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2

/-!
# The six-qubit code `C₆`, `[[6, 2, 2]]`: logical operators

The logical basis of `SixQubit_6_2_2.stabilizerCode`:
```
X̄₁ = IIXXII   (weight 2, support {2,3})
Z̄₁ = ZIIZZI   (weight 3, support {0,3,4})
X̄₂ = IXIXXI   (weight 3, support {1,3,4})
Z̄₂ = IIIIZZ   (weight 2, support {4,5})
```
The first logical qubit has its short operator on the `X` side, the second on
the `Z` side. `X̄₁` anticommutes with `Z̄₁` (shared qubit 3) and `X̄₂` with
`Z̄₂` (shared qubit 4); every other pair commutes (an even overlap, or the same
type).

## Outline

- Logical operators `logicalX_1`, `logicalX_2`, `logicalZ_1`, `logicalZ_2`
- Anticommutation `logicalX_1_anticommutes_logicalZ_1`,
  `logicalX_2_anticommutes_logicalZ_2`
- Centralizer membership `logicalX_ℓ_mem_centralizer`,
  `logicalZ_ℓ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[6, 2]]ₗ`
-/

namespace Quantum
namespace StabilizerGroup
namespace SixQubit_6_2_2

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- Logical X for logical qubit 1: `IIXXII` (X on qubits 2, 3). -/
def logicalX_1 : NQubitPauliGroupElement 6 := σ[IIXXII]

/-- Logical X for logical qubit 2: `IXIXXI` (X on qubits 1, 3, 4). -/
def logicalX_2 : NQubitPauliGroupElement 6 := σ[IXIXXI]

/-- Logical Z for logical qubit 1: `ZIIZZI` (Z on qubits 0, 3, 4). -/
def logicalZ_1 : NQubitPauliGroupElement 6 := σ[ZIIZZI]

/-- Logical Z for logical qubit 2: `IIIIZZ` (Z on qubits 4, 5). -/
def logicalZ_2 : NQubitPauliGroupElement 6 := σ[IIIIZZ]

/-! ## Anticommutation -/

/-- `X̄₁ = IIXXII` and `Z̄₁ = ZIIZZI` anticommute: they meet on qubit 3 only. -/
lemma logicalX_1_anticommutes_logicalZ_1 : Anticommute logicalX_1 logicalZ_1 := by
  decide

/-- `X̄₂ = IXIXXI` and `Z̄₂ = IIIIZZ` anticommute: they meet on qubit 4 only. -/
lemma logicalX_2_anticommutes_logicalZ_2 : Anticommute logicalX_2 logicalZ_2 := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the four generators, a
closed statement that `decide` settles. Against a Z-check, an X-type logical
meets it in an even number of qubits (`X̄₁`: `{2,3}` and `∅`; `X̄₂`: `{1,3}` and
`{1,4}`), and dually for the Z-type logicals against the X-checks. -/

/-- `X̄₁ = IIXXII` commutes with every element of the stabilizer. -/
lemma logicalX_1_mem_centralizer : logicalX_1 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `X̄₂ = IXIXXI` commutes with every element of the stabilizer. -/
lemma logicalX_2_mem_centralizer : logicalX_2 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄₁ = ZIIZZI` commutes with every element of the stabilizer. -/
lemma logicalZ_1_mem_centralizer : logicalZ_1 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄₂ = IIIIZZ` commutes with every element of the stabilizer. -/
lemma logicalZ_2_mem_centralizer : logicalZ_2 ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-! ## The code with its logical basis `Code[[6, 2]]ₗ` -/

/-- The `C₆` code with its logical basis `(X̄₁, Z̄₁)`, `(X̄₂, Z̄₂)`. The
operators of distinct logical qubits commute: `X̄₁` and `Z̄₂` have disjoint
supports, `X̄₂` and `Z̄₁` meet on qubits 3 and 4, and the others have the same
type. -/
noncomputable def stabilizerCodeWithLogicals : Code[[6, 2]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps
    | 0 => ⟨logicalX_1, logicalZ_1, logicalX_1_mem_centralizer, logicalZ_1_mem_centralizer,
        logicalX_1_anticommutes_logicalZ_1⟩
    | 1 => ⟨logicalX_2, logicalZ_2, logicalX_2_mem_centralizer, logicalZ_2_mem_centralizer,
        logicalX_2_anticommutes_logicalZ_2⟩
  logical_commute_cross := by decide

end SixQubit_6_2_2
end StabilizerGroup
end Quantum

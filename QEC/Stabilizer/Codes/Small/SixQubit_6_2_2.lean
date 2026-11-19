module

public import Mathlib.Tactic
public import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
public import QEC.Stabilizer.Foundations.PauliGroup.Commutation
public import QEC.Stabilizer.Foundations.PauliGroup.Notation
public import QEC.Stabilizer.Framework.Core.CodeNotation
public import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
public import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
public import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
public import QEC.Stabilizer.Framework.Symplectic.DistanceDecide
public import QEC.Stabilizer.Framework.Symplectic.Presentation
public import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

/-!
# The six-qubit code `C₆`, `[[6, 2, 2]]`

Knill's `C₆` code: a six-qubit self-dual CSS stabilizer code encoding two
logical qubits, with code distance 2. Arrange the qubits in three pairs
`{0, 1}`, `{2, 3}`, `{4, 5}`. The four generators (`n − k = 4`), each of weight
four, are `Z` and `X` on the first two pairs and on the first and last pair:
```
Z1 = Z Z Z Z I I
Z2 = Z Z I I Z Z
X1 = X X X X I I
X2 = X X I I X X
```

The code is packaged by the **decide route**: the four generators form a literal
list, and pairwise commutation, phase zero and check-matrix independence are
closed statements settled by `decide`; `−I ∉ closure` follows by
`negIdentity_not_mem_of_indep_phase_zero_commute`.

Distance 2 is `hasCodeDistance_of_decide`, both checks decided: every weight-1
Pauli anticommutes with a Z-check (local `X` or `Y`) or an X-check (local `Z`)
covering its qubit, and `IIXXII` is a nontrivial logical of weight 2.

The logical basis `X̄₁ = IIXXII`, `X̄₂ = IXIXXI`, `Z̄₁ = ZIIZZI`,
`Z̄₂ = IIIIZZ` is in `SixQubit_6_2_2Logicals.lean`.

## Outline

- Generators `Z1`, `Z2`, `X1`, `X2` and the list `generatorsList`
- `presentation` (fields decided inline), `stabilizerCode : Code[[6, 2]]`
- Distance 2 (decided weight-2 logical witness, no weight-1 logical):
  `minWeightLogical`, `code_has_distance_two`,
  `stabilizerCodeWithDistance : Code[[6, 2, 2]]`
-/

@[expose] public section

namespace Quantum
namespace StabilizerGroup
namespace SixQubit_6_2_2

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Generators -/

/-- First Z-check stabilizer: `ZZZZII` (Z on qubits 0, 1, 2, 3). -/
def Z1 : NQubitPauliGroupElement 6 := σ[ZZZZII]

/-- Second Z-check stabilizer: `ZZIIZZ` (Z on qubits 0, 1, 4, 5). -/
def Z2 : NQubitPauliGroupElement 6 := σ[ZZIIZZ]

/-- First X-check stabilizer: `XXXXII` (X on qubits 0, 1, 2, 3). -/
def X1 : NQubitPauliGroupElement 6 := σ[XXXXII]

/-- Second X-check stabilizer: `XXIIXX` (X on qubits 0, 1, 4, 5). -/
def X2 : NQubitPauliGroupElement 6 := σ[XXIIXX]

/-- The four generators as a list (Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 6) :=
  [Z1, Z2, X1, X2]

/-! ## The bare code `Code[[6, 2]]`

Four independent, pairwise commuting generators on six qubits: two logical
qubits.

Every Z-check meets every X-check in an even number of qubits: `Z1` and `X1`
in `{0,1,2,3}`, `Z1` and `X2` in `{0,1}`, `Z2` and `X1` in `{0,1}`, `Z2` and
`X2` in `{0,1,4,5}`. `decide` checks the sixteen ordered pairs, the phases, and
the check-matrix rank. -/

/-- The generator list as a presentation of a `[[6, 2]]` code: its 4
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 6 2 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := by decide
  generators_independent := by decide
  generators_commute := by decide

/-- The `C₆` code as a stabilizer code `[[6, 2]]`. -/
noncomputable def stabilizerCode : Code[[6, 2]] := presentation.toCode

/-! ## Distance 2

Distance 2 is two decided checks (`hasCodeDistance_of_decide`).
`IIXXII` meets `Z1` on two qubits and `Z2` on none, so it commutes with every
check, and it is not a product of checks up to phase. A local `X` or `Y`
anticommutes with the `Z` of `Z1` on `{0,1,2,3}` or of `Z2` on `{4,5}`; a local
`Z` with the `X` of `X1` or `X2`. -/

/-- `IIXXII`: a nontrivial logical of weight 2. -/
def minWeightLogical : NQubitPauliGroupElement 6 := σ[IIXXII]

/-- **The `C₆` code has distance 2.** `IIXXII` is a nontrivial logical of
weight 2, and every weight-1 Pauli anticommutes with some generator. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  presentation.hasCodeDistance_of_decide minWeightLogical (by decide +kernel) (by decide +kernel)

/-- The `C₆` code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[6, 2, 2]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_two

end SixQubit_6_2_2
end StabilizerGroup
end Quantum

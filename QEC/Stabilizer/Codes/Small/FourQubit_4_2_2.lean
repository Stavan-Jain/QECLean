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
# The four-qubit code `[[4, 2, 2]]`

The four-qubit detection code, also known as `C₄`: a self-dual CSS stabilizer
code encoding two logical qubits, with code distance 2. Its codespace is
spanned by the four even-parity states `(|x⟩ + |x̄⟩)/√2`, where `x̄` is the
bitwise complement of `x`, and its two generators (`n − k = 2`) are `ZZZZ` and
`XXXX`.

The code is packaged by the **decide route**: the two generators form a literal
list, and pairwise commutation, phase zero and check-matrix independence are
closed statements settled by `decide`; `−I ∉ closure` follows by
`negIdentity_not_mem_of_indep_phase_zero_commute`.

Distance 2 is `hasCodeDistance_of_decide`, both checks decided: every weight-1
Pauli anticommutes with `ZZZZ` (local `X` or `Y`) or `XXXX` (local `Z`), and
`IXIX` is a nontrivial logical of weight 2.

The logical basis `X̄₁ = IXIX`, `X̄₂ = IIXX`, `Z̄₁ = IIZZ`, `Z̄₂ = IZIZ` is in
`FourQubit_4_2_2Logicals.lean`.

## Outline

- Generators `Z1`, `X1` and the list `generatorsList`
- `presentation` (fields decided inline), `stabilizerCode : Code[[4, 2]]`
- Distance 2 (decided weight-2 logical witness, no weight-1 logical):
  `minWeightLogical`, `code_has_distance_two`,
  `stabilizerCodeWithDistance : Code[[4, 2, 2]]`
-/

@[expose] public section

namespace Quantum
namespace StabilizerGroup
namespace FourQubit_4_2_2

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Generators -/

/-- Z-check stabilizer: `ZZZZ` (Z on every qubit). -/
def Z1 : NQubitPauliGroupElement 4 := σ[ZZZZ]

/-- X-check stabilizer: `XXXX` (X on every qubit). -/
def X1 : NQubitPauliGroupElement 4 := σ[XXXX]

/-- The two generators as a list (Z-check first, then X-check). -/
def generatorsList : List (NQubitPauliGroupElement 4) :=
  [Z1, X1]

/-! ## The bare code `Code[[4, 2]]`

Two independent, commuting generators on four qubits: two logical qubits.

`ZZZZ` and `XXXX` anticommute locally at all four qubits — an even count, so
they commute. `decide` checks the four ordered pairs, the phases, and the
check-matrix rank. -/

/-- The generator list as a presentation of a `[[4, 2]]` code: its 2
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 4 2 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := by decide
  generators_independent := by decide
  generators_commute := by decide

/-- The `[[4, 2, 2]]` code as a stabilizer code `[[4, 2]]`. -/
noncomputable def stabilizerCode : Code[[4, 2]] := presentation.toCode

/-! ## Distance 2

Distance 2 is two decided checks (`hasCodeDistance_of_decide`).
`IXIX` meets `ZZZZ` on two qubits, so it commutes with both checks, and it
is not a product of checks up to phase. A local `X` or `Y` anticommutes with
the `Z` of `ZZZZ`, and a local `Z` with the `X` of `XXXX`, whatever the
qubit. -/

/-- `IXIX`: a nontrivial logical of weight 2. -/
def minWeightLogical : NQubitPauliGroupElement 4 := σ[IXIX]

/-- **The `[[4, 2, 2]]` code has distance 2.** `IXIX` is a nontrivial logical of
weight 2, and every weight-1 Pauli anticommutes with some generator. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  presentation.hasCodeDistance_of_decide minWeightLogical (by decide +kernel) (by decide +kernel)

/-- The `[[4, 2, 2]]` code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[4, 2, 2]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_two

end FourQubit_4_2_2
end StabilizerGroup
end Quantum

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
# The LNCY code `[[4, 1, 2]]`

The Leung–Nielsen–Chuang–Yamamoto code is a four-qubit CSS stabilizer code
encoding one logical qubit, with code distance 2: it detects, but does not
correct, a single arbitrary Pauli error. Its codewords are
```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2
|1_L⟩ = (|0011⟩ + |1100⟩)/√2
```
and its three generators (`n − k = 3`) are the ones that stabilize them: `ZZII`,
`IIZZ` and `XXXX`. The tableau with `X` and `Z` exchanged, `XXII`, `IIXX` and
`ZZZZ`, stabilizes a different two-dimensional subspace; the convention here is
fixed by the codewords above.

The code is packaged by the **decide route**: the three generators form a
literal list, and pairwise commutation, phase zero and check-matrix
independence are closed statements settled by `decide`; `−I ∉ closure` follows
by `negIdentity_not_mem_of_indep_phase_zero_commute`.

Distance 2 is `hasCodeDistance_of_decide`, both checks decided: every weight-1
Pauli anticommutes with `ZZII` or `IIZZ` (local `X` or `Y`, depending on the
qubit) or with `XXXX` (local `Z`), and `XXII` is a nontrivial logical of
weight 2.

The logical basis `X̄ = XXII`, `Z̄ = ZIZI` is in `CSS_4_1_2Logicals.lean`.

## Outline

- Generators `Z1`, `Z2`, `X1` and the list `generatorsList`
- `presentation` (fields decided inline), `stabilizerCode : Code[[4, 1]]`
- Distance 2 (decided weight-2 logical witness, no weight-1 logical):
  `minWeightLogical`, `code_has_distance_two`,
  `stabilizerCodeWithDistance : Code[[4, 1, 2]]`
-/

@[expose] public section

namespace Quantum
namespace StabilizerGroup
namespace CSS_4_1_2

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Generators -/

/-- First Z-check stabilizer: `ZZII` (Z on qubits 0, 1). -/
def Z1 : NQubitPauliGroupElement 4 := σ[ZZII]

/-- Second Z-check stabilizer: `IIZZ` (Z on qubits 2, 3). -/
def Z2 : NQubitPauliGroupElement 4 := σ[IIZZ]

/-- X-check stabilizer: `XXXX` (X on every qubit). -/
def X1 : NQubitPauliGroupElement 4 := σ[XXXX]

/-- The three generators as a list (Z-checks first, then X-check). -/
def generatorsList : List (NQubitPauliGroupElement 4) :=
  [Z1, Z2, X1]

/-! ## The bare code `Code[[4, 1]]`

Three independent, pairwise commuting generators on four qubits: one logical
qubit.

`ZZII` meets `XXXX` on qubits 0 and 1 and `IIZZ` meets it on qubits 2 and 3 —
both even, so all pairs commute. `decide` checks the nine ordered pairs, the
phases, and the check-matrix rank. -/

/-- The generator list as a presentation of a `[[4, 1]]` code: its 3
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 4 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := by decide
  generators_independent := by decide
  generators_commute := by decide

/-- The LNCY code as a stabilizer code `[[4, 1]]`. -/
noncomputable def stabilizerCode : Code[[4, 1]] := presentation.toCode

/-! ## Distance 2

Distance 2 is two decided checks (`hasCodeDistance_of_decide`).
`XXII` meets `ZZII` on two qubits and `IIZZ` on none, so it commutes with
every check, and it is not a product of checks up to phase. A local `X` or `Y`
anticommutes with the `Z` of `ZZII` on qubits 0, 1 or of `IIZZ` on qubits 2, 3;
a local `Z` with the `X` of `XXXX`. -/

/-- `XXII`: a nontrivial logical of weight 2. -/
def minWeightLogical : NQubitPauliGroupElement 4 := σ[XXII]

/-- **The LNCY code has distance 2.** `XXII` is a nontrivial logical of
weight 2, and every weight-1 Pauli anticommutes with some generator. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  presentation.hasCodeDistance_of_decide minWeightLogical (by decide +kernel) (by decide +kernel)

/-- The LNCY code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[4, 1, 2]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_two

end CSS_4_1_2
end StabilizerGroup
end Quantum

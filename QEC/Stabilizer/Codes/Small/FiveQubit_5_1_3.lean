module

public import Mathlib.Tactic
public import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
public import QEC.Stabilizer.Foundations.PauliGroup.Commutation
public import QEC.Stabilizer.Foundations.PauliGroup.Notation
public import QEC.Stabilizer.Framework.Core.CodeNotation
public import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
public import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
public import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
public import QEC.Stabilizer.Framework.Symplectic.Presentation
public import QEC.Stabilizer.Framework.Symplectic.DistanceDecide
public import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

/-!
# The five-qubit code `[[5, 1, 3]]`

The five-qubit perfect code: the smallest stabilizer code that corrects an
arbitrary single-qubit error. It encodes one logical qubit in five physical
qubits with code distance 3, saturating the quantum Hamming bound. Its four
generators (`n − k = 4`) are the cyclic shifts of `XZZXI`:
- `g1 = XZZXI`
- `g2 = IXZZX`
- `g3 = XIXZZ`
- `g4 = ZXIXZ`

The code is not CSS: each generator carries both `X` and `Z` factors, so there
is no split into Z-checks and X-checks. The **decide route** never looks at
that split: the four generators form a literal list, and pairwise commutation,
phase zero and check-matrix independence are closed statements settled by
`decide`; `−I ∉ closure` follows by
`negIdentity_not_mem_of_indep_phase_zero_commute`.

Distance 3 is `hasCodeDistance_of_decide`: `IYYIX` is a nontrivial logical of
weight 3, and every weight-1 Pauli (15 cases) and every weight-2 Pauli
(90 cases) anticommutes with some generator. Both are decided.

The logical basis `X̄ = X⊗⁵`, `Z̄ = Z⊗⁵` is in `FiveQubit_5_1_3Logicals.lean`.

## Outline

- Generators `g1`–`g4` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `presentation`, `stabilizerCode : Code[[5, 1]]`
- Distance 3 (decided weight-3 logical witness, no lighter logical):
  `minWeightLogical`, `code_has_distance_three`, `stabilizerCodeWithDistance : Code[[5, 1, 3]]`
-/

@[expose] public section

namespace Quantum
namespace StabilizerGroup
namespace FiveQubit_5_1_3

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Generators -/

/-- First generator: `XZZXI`. -/
def g1 : NQubitPauliGroupElement 5 := σ[XZZXI]

/-- Second generator: `IXZZX` (cyclic shift of `g1` by 1). -/
def g2 : NQubitPauliGroupElement 5 := σ[IXZZX]

/-- Third generator: `XIXZZ` (cyclic shift of `g1` by 2). -/
def g3 : NQubitPauliGroupElement 5 := σ[XIXZZ]

/-- Fourth generator: `ZXIXZ` (cyclic shift of `g1` by 3). -/
def g4 : NQubitPauliGroupElement 5 := σ[ZXIXZ]

/-- The four generators as a list. -/
def generatorsList : List (NQubitPauliGroupElement 5) :=
  [g1, g2, g3, g4]

/-! ## Decided hypotheses

Every pair of generators anticommutes locally on exactly two qubits (`g1`, `g2`
on `{1,3}`; `g1`, `g3` on `{2,3}`; `g1`, `g4` on `{0,1}`; `g2`, `g3` on
`{2,4}`; `g2`, `g4` on `{3,4}`; `g3`, `g4` on `{0,3}`), so they commute.
`decide` checks the sixteen ordered pairs, the phases, and the check-matrix
rank. -/

/-- All four generators pairwise commute. -/
lemma generators_commute :
    ∀ g ∈ generatorsList, ∀ h ∈ generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the four generators are linearly independent. -/
lemma rowsLinearIndependent_generatorsList : rowsLinearIndependent generatorsList := by
  decide

/-! ## The bare code `Code[[5, 1]]`

Four independent, pairwise commuting generators on five qubits: one logical
qubit. -/

/-- The generator list as a presentation of a `[[5, 1]]` code: its 4
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 5 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := rowsLinearIndependent_generatorsList
  generators_commute := generators_commute

/-- The five-qubit code as a stabilizer code `[[5, 1]]`. -/
noncomputable def stabilizerCode : Code[[5, 1]] := presentation.toCode

/-! ## Distance 3

Distance 3 is two decided checks (`hasCodeDistance_of_decide`). `IYYIX`, the
operator part of `X⊗⁵ · g1`, commutes with every generator and is not a product
of generators up to phase. Every weight-one and weight-two Pauli anticommutes
with some generator. -/

/-- `IYYIX`: a nontrivial logical of weight 3. -/
def minWeightLogical : NQubitPauliGroupElement 5 := σ[IYYIX]

/-- **The five-qubit code has distance 3.** `IYYIX` is a nontrivial logical of
weight 3, and every Pauli of weight 1 or 2 anticommutes with some generator. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  presentation.hasCodeDistance_of_decide minWeightLogical (by decide +kernel) (by decide +kernel)

/-- The five-qubit code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[5, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three

end FiveQubit_5_1_3
end StabilizerGroup
end Quantum

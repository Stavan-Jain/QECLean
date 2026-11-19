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
# Shor's code `[[9, 1, 3]]`

Shor's nine-qubit code: a repetition code of cat states, a CSS stabilizer code
encoding one logical qubit, with code distance 3. The nine qubits form three
blocks `{0,1,2}`, `{3,4,5}`, `{6,7,8}`. Of the eight generators (`n − k = 8`),
six Z-checks `ZZ` on adjacent qubits of a block catch bit flips within the
block, and two X-checks, `X` on the first two blocks and on the last two,
compare the blocks' phases.

The code is packaged by the **decide route**: the eight generators form a
literal list, and pairwise commutation, phase zero and check-matrix
independence are closed statements settled by `decide`; `−I ∉ closure` follows
by `negIdentity_not_mem_of_indep_phase_zero_commute`.

Shor's code is *degenerate*: it has weight-two errors that no check detects,
yet its distance is three. The two X-checks do not separate qubits within a
block, so `Z_i Z_j` on two qubits of one block commutes with every check — but
such a `Z_i Z_j` is itself a stabilizer (a `ZZ` check, or the product of a
block's two), so it is not a logical. Distance 3 is `hasCodeDistance_of_decide`,
whose lower-bound check accepts exactly that escape: every weight-one or
weight-two Pauli is detected by some check or is a stabilizer up to phase. `X`
on the first block is a nontrivial logical of weight 3.

The logical basis `X̄ = Z⊗⁹`, `Z̄ = X⊗⁹` is in `Shor9Logicals.lean`.

## Outline

- Generators `Z1`–`Z6`, `X1`, `X2` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `presentation`, `stabilizerCode : Code[[9, 1]]`
- Distance 3 (decided weight-3 logical witness, no lighter logical):
  `minWeightLogical`, `code_has_distance_three`,
  `stabilizerCodeWithDistance : Code[[9, 1, 3]]`
-/

@[expose] public section

namespace Quantum
namespace StabilizerGroup
namespace Shor9

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Generators -/

/-- First Z-check stabilizer: `ZZIIIIIII` (Z on qubits 0, 1 of the first
block). -/
def Z1 : NQubitPauliGroupElement 9 := σ[ZZIIIIIII]

/-- Second Z-check stabilizer: `IZZIIIIII` (Z on qubits 1, 2 of the first
block). -/
def Z2 : NQubitPauliGroupElement 9 := σ[IZZIIIIII]

/-- Third Z-check stabilizer: `IIIZZIIII` (Z on qubits 3, 4 of the second
block). -/
def Z3 : NQubitPauliGroupElement 9 := σ[IIIZZIIII]

/-- Fourth Z-check stabilizer: `IIIIZZIII` (Z on qubits 4, 5 of the second
block). -/
def Z4 : NQubitPauliGroupElement 9 := σ[IIIIZZIII]

/-- Fifth Z-check stabilizer: `IIIIIIZZI` (Z on qubits 6, 7 of the third
block). -/
def Z5 : NQubitPauliGroupElement 9 := σ[IIIIIIZZI]

/-- Sixth Z-check stabilizer: `IIIIIIIZZ` (Z on qubits 7, 8 of the third
block). -/
def Z6 : NQubitPauliGroupElement 9 := σ[IIIIIIIZZ]

/-- First X-check stabilizer: `XXXXXXIII` (X on the first two blocks). -/
def X1 : NQubitPauliGroupElement 9 := σ[XXXXXXIII]

/-- Second X-check stabilizer: `IIIXXXXXX` (X on the last two blocks). -/
def X2 : NQubitPauliGroupElement 9 := σ[IIIXXXXXX]

/-- The eight generators as a list (Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 9) :=
  [Z1, Z2, Z3, Z4, Z5, Z6, X1, X2]

/-! ## Decided hypotheses

Each Z-check meets each X-check in either zero or two qubits, and same-type
generators commute componentwise. `decide` checks the 64 ordered pairs and the
phases. For the check-matrix rank, eight rows on nine qubits, plain `decide`
runs out of heartbeats, so the check is handed straight to the kernel with
`decide +kernel`. -/

/-- All eight generators pairwise commute. -/
lemma generators_commute :
    ∀ g ∈ generatorsList, ∀ h ∈ generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the eight generators are linearly independent. -/
lemma rowsLinearIndependent_generatorsList : rowsLinearIndependent generatorsList := by
  decide +kernel

/-! ## The bare code `Code[[9, 1]]`

Eight independent, pairwise commuting generators on nine qubits: one logical
qubit. -/

/-- The generator list as a presentation of a `[[9, 1]]` code: its 8
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 9 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := rowsLinearIndependent_generatorsList
  generators_commute := generators_commute

/-- Shor's code as a stabilizer code `[[9, 1]]`. -/
noncomputable def stabilizerCode : Code[[9, 1]] := presentation.toCode

/-- The stabilizer code's subgroup is the closure of the generator list. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-! ## Distance 3

Distance 3 is two decided checks (`hasCodeDistance_of_decide`). `X` on the
first block, `{0, 1, 2}`, is `X⊗⁹ · X2`: it commutes with every check, and it
is not a product of checks up to phase. Every weight-one and weight-two Pauli
either anticommutes with some check or is itself a stabilizer up to phase. The
second case is where the code's degeneracy goes: `Z_i Z_j` on two qubits of one
block slips past both X-checks, but it is a `ZZ` check or the product of a
block's two. -/

/-- `XXXIIIIII`: a nontrivial logical of weight 3. -/
def minWeightLogical : NQubitPauliGroupElement 9 := σ[XXXIIIIII]

/-- **Shor's code has distance 3.** `XXXIIIIII` is a nontrivial logical of
weight 3, and every Pauli of weight 1 or 2 is detected by some check or is a
stabilizer up to phase. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  presentation.hasCodeDistance_of_decide minWeightLogical (by decide +kernel) (by decide +kernel)

/-- Shor's code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[9, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three

end Shor9
end StabilizerGroup
end Quantum

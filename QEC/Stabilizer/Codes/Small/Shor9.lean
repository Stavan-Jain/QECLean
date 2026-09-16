import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace Shor9

/-!
# Shor’s 9-qubit code (stabilizer generators)

This file defines a clean, reusable formalization of Shor’s 9-qubit stabilizer
subgroup:

- Z-type generators `M1`–`M6` (pairwise Z checks within blocks)
- X-type generators `M7`,`M8` (blockwise X checks)

and packages it by the **decide route**: the eight generators form a literal
list, and pairwise commutation, phase zero and linear independence of the
check-matrix rows are closed decidable statements settled by `decide`. From
those, `−I ∉ closure` follows by
`negIdentity_not_mem_of_indep_phase_zero_commute`, and the code is bundled as
`stabilizerCode : Code[[9, 1]]`.

## Outline

- Generators `M1`–`M8` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `stabilizerCode : Code[[9, 1]]`
-/

open NQubitPauliGroupElement

/-!
## Generator definitions

Qubits are indexed `0..8` in three blocks `{0,1,2}`, `{3,4,5}`, `{6,7,8}`.
`M1`–`M6` are **intra-block** Z⊗Z on adjacent pairs within each block of three.
`M7` is X on all qubits `0..5`; `M8` is X on all qubits `3..8` (standard Shor
CSS presentation; overlapping supports).
-/

/-- Z⊗Z on qubits 0 and 1 (first block, adjacent pair). -/
def M1 : NQubitPauliGroupElement 9 := σ[ZZIIIIIII]

/-- Z⊗Z on qubits 1 and 2 (first block, adjacent pair). -/
def M2 : NQubitPauliGroupElement 9 := σ[IZZIIIIII]

/-- Z⊗Z on qubits 3 and 4 (second block). -/
def M3 : NQubitPauliGroupElement 9 := σ[IIIZZIIII]

/-- Z⊗Z on qubits 4 and 5 (second block). -/
def M4 : NQubitPauliGroupElement 9 := σ[IIIIZZIII]

/-- Z⊗Z on qubits 6 and 7 (third block). -/
def M5 : NQubitPauliGroupElement 9 := σ[IIIIIIZZI]

/-- Z⊗Z on qubits 7 and 8 (third block). -/
def M6 : NQubitPauliGroupElement 9 := σ[IIIIIIIZZ]

/-- X on each of qubits 0–5 (six-qubit X stabilizer, overlapping first two
blocks). -/
def M7 : NQubitPauliGroupElement 9 := σ[XXXXXXIII]

/-- X on each of qubits 3–8 (six-qubit X stabilizer, overlapping last two
blocks). -/
def M8 : NQubitPauliGroupElement 9 := σ[IIIXXXXXX]

/-- The eight generators as a list (Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 9) :=
  [M1, M2, M3, M4, M5, M6, M7, M8]

/-!
## Decided hypotheses

Each Z-check meets each X-check in either zero or two qubits, and same-type
generators commute componentwise; `decide` checks all 64 ordered pairs.
-/

/-- All eight generators pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the eight generators are linearly independent.
Eight rows on nine qubits is the largest instance among the small codes, and
plain `decide` runs out of heartbeats on it, so the check is handed straight to
the kernel. -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide +kernel

/-- The Shor generator list is an independent generating set. -/
theorem GeneratorsIndependent_9_generatorsList : GeneratorsIndependent 9 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-!
## `-I` is not in the Shor-9 stabilizer subgroup
-/

/-- The closure of the eight generators does not contain −I. -/
theorem negIdentity_not_mem :
    negIdentity 9 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-!
## Bundled `StabilizerGroup 9` and `Code[[9, 1]]`
-/

/-- Shor's code as `StabilizerGroup 9` (canonical: from generator list). -/
noncomputable def stabilizerGroup : StabilizerGroup 9 :=
  mkStabilizerFromGenerators 9 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-- Shor's code as a stabilizer code [[9, 1]]: eight independent generators on
nine qubits, hence one logical qubit. -/
noncomputable def stabilizerCode : Code[[9, 1]] where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_9_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

end Shor9
end StabilizerGroup

end Quantum

import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Symplectic.Presentation
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace SixQubit_6_2_2

/-!
# Knill's `C₆` code `[[6, 2, 2]]`

A six-qubit normal self-dual CSS stabilizer code encoding **two logical qubits**
with code distance 2. Originally introduced in [E. Knill, *Quantum computing
with realistically noisy devices*, Nature 434, 39 (2005);
`arxiv:quant-ph/0410199`], where it serves as the outer code in Knill's C₄/C₆
fault-tolerant architecture (with `[[4,2,2]]` at the inner level).

The stabilizer tableau (Knill / EC Zoo / Qiskit preset ID 126) is
```
Z1 = Z Z Z Z I I
Z2 = Z Z I I Z Z
X1 = X X X X I I
X2 = X X I I X X
```
Uniform-weight-4 generators, `n − k = 4`. Each stabilizer corresponds to a
square face of a triangular-prism ladder (3 rungs, periodic boundary).

Equivalence notes: the Ganti–Onunkwo–Young code at `r = 1`, the
`[[k+4, k, 2]]` H code at `k = 2`, and the Khesin–Lu–Shor code at
`r = 2, m = 3` are all the C₆ code (none formalized here). The `[[4, 2, 2]]`
code (`FourQubit_4_2_2.lean`) is its structural sibling in Knill's C₄/C₆
concatenation.

The code is packaged by the **decide route**: the four generators form a literal
list, and pairwise commutation, phase zero and check-matrix independence are
closed statements settled by `decide`; `−I ∉ closure` follows by
`negIdentity_not_mem_of_indep_phase_zero_commute`.

Distance 2 is `hasCodeDistance_two_of_anticommute_witness`: every weight-1
Pauli anticommutes with a Z-check (local `X` or `Y`) or an X-check (local `Z`)
covering its qubit, and `IIXXII` is a nontrivial logical of weight 2.

The logical basis (Knill's "L" and "S" pairs) is in
`SixQubit_6_2_2Logicals.lean`.

## Outline

- Generators `Z1`, `Z2`, `X1`, `X2` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `stabilizerCode : Code[[6, 2]]`
- Distance 2 (weight-1 anti-witness table, weight-2 witness):
  `code_has_distance_two`, `stabilizerCodeWithDistance : Code[[6, 2, 2]]`
-/

open NQubitPauliGroupElement

/-! ## Generators

Qubit indexing is 0-based; qubits 0, 1 are the "top" pair, 2, 3 the "middle"
pair, 4, 5 the "bottom" pair. -/

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

/-! ## Decided hypotheses

Every Z-check meets every X-check in an even number of qubits: `Z1` and `X1`
in `{0,1,2,3}`, `Z1` and `X2` in `{0,1}`, `Z2` and `X1` in `{0,1}`, `Z2` and
`X2` in `{0,1,4,5}`. `decide` checks the sixteen ordered pairs, the phases, and
the check-matrix rank. -/

/-- All four generators pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the four generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_6_generatorsList : GeneratorsIndependent 6 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-! ## No `−I` in the stabilizer subgroup -/

/-- The closure of the four generators does not contain `−I`. -/
theorem negIdentity_not_mem :
    negIdentity 6 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-! ## Bundled `StabilizerGroup 6` -/

/-- The C₆ stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 6 :=
  mkStabilizerFromGenerators 6 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-! ## The bare code `Code[[6, 2]]`

Four independent, pairwise commuting generators on six qubits: two logical
qubits. -/

/-- The generator list as a presentation of a `[[6, 2]]` code: its 4
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 6 2 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := rowsLinearIndependent_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- The C₆ code as a stabilizer code `[[6, 2]]`. -/
noncomputable def stabilizerCode : Code[[6, 2]] := presentation.toCode

/-- The stabilizer code's subgroup is the closure of the generator list. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-! ## Distance 2

### No nontrivial logical of weight 1

The qubits split into three pairs. A local `X` or `Y` anticommutes with the `Z`
of `Z1` on `{0,1,2,3}` and of `Z2` on `{4,5}`; a local `Z` anticommutes with
the `X` of `X1` on `{0,1,2,3}` and of `X2` on `{4,5}`. `first` picks whichever
check covers the qubit. -/

/-- Every weight-1 Pauli anticommutes with some generator. -/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 6, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ listToSet generatorsList, Anticommute (weightOneAt i P) g := by
  intro i P hP
  fin_cases i <;>
    (match P, hP with
    | PauliOperator.X, _ => first
      | exact ⟨Z1, by simp [generatorsList], by decide⟩
      | exact ⟨Z2, by simp [generatorsList], by decide⟩
    | PauliOperator.Y, _ => first
      | exact ⟨Z1, by simp [generatorsList], by decide⟩
      | exact ⟨Z2, by simp [generatorsList], by decide⟩
    | PauliOperator.Z, _ => first
      | exact ⟨X1, by simp [generatorsList], by decide⟩
      | exact ⟨X2, by simp [generatorsList], by decide⟩
    | PauliOperator.I, hP => exact (hP rfl).elim)

/-! ### A nontrivial logical of weight 2

`IIXXII` meets `Z1` on two qubits and `Z2` on none, so it commutes with every
check; it anticommutes with `ZIIZZI` (one shared qubit), which meets `X1` and
`X2` on two qubits each and so also commutes with every check. -/

/-- `IIXXII`: a nontrivial logical of weight 2. -/
def minWeightLogical : NQubitPauliGroupElement 6 := σ[IIXXII]

/-- `ZIIZZI`: a centralizer element anticommuting with `minWeightLogical`. -/
def minWeightPartner : NQubitPauliGroupElement 6 := σ[ZIIZZI]

lemma minWeightLogical_weight : weight minWeightLogical = 2 := by decide

lemma minWeightLogical_mem_centralizer : minWeightLogical ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

lemma minWeightPartner_mem_centralizer : minWeightPartner ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `IIXXII` and `ZIIZZI` meet on qubit 3 only, an odd number. -/
lemma minWeightLogical_anticommutes_minWeightPartner :
    Anticommute minWeightLogical minWeightPartner := by decide

/-- `IIXXII` is a nontrivial logical operator: it lies in the centralizer and
anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial :
    IsNontrivialLogicalOperator minWeightLogical stabilizerCode.toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ minWeightLogical_mem_centralizer
    minWeightPartner_mem_centralizer minWeightLogical_anticommutes_minWeightPartner

/-! ### The code with its distance `Code[[6, 2, 2]]` -/

/-- **The C₆ code has distance 2.** Every weight-1 Pauli anticommutes with some
generator, and `IIXXII` is a nontrivial logical of weight 2. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode (listToSet generatorsList)
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨minWeightLogical, minWeightLogical_isNontrivial, minWeightLogical_weight⟩

/-- The C₆ code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[6, 2, 2]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_two

end SixQubit_6_2_2
end StabilizerGroup

end Quantum

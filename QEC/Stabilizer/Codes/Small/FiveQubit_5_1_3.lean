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
namespace FiveQubit_5_1_3

/-!
# The five-qubit perfect code `[[5, 1, 3]]`

The smallest stabilizer code that corrects an arbitrary single-qubit error
[Laflamme–Miquel–Paz–Zurek 1996, `arxiv:quant-ph/9602019`;
Bennett–DiVincenzo–Smolin–Wootters 1996, `arxiv:quant-ph/9604024`]. It encodes
`k = 1` logical qubit in `n = 5` physical qubits with distance `d = 3`,
saturating the quantum Hamming bound. The generators are the cyclic shifts of
`XZZXI` (EC Zoo `stab_5_1_3`, cross-referenced with Qiskit preset ID 21):
- `g1 = XZZXI`
- `g2 = IXZZX`
- `g3 = XIXZZ`
- `g4 = ZXIXZ`

This is the **first non-CSS code** in the repository: each generator carries
both `X` and `Z` factors, so there is no Z/X split. That changes nothing up to
the bare code — the **decide route** never looks at the split: the four
generators form a literal list, pairwise commutation, phase zero and
check-matrix independence are closed statements settled by `decide`, and
`−I ∉ closure` follows by `negIdentity_not_mem_of_indep_phase_zero_commute`.

It does change the distance argument, since the CSS closers no longer apply.
Distance 3 goes through the general `hasCodeDistance_of`: kernel-checked
anti-witness tables rule out nontrivial logicals of weight 1 (15 cases, via
`no_weight_one_mem_centralizer_of_anticommute_witness`) and weight 2 (90 cases,
via `no_weight_two_mem_centralizer_of_anticommute_witness`), and `IYYIX` is a
nontrivial logical of weight 3. See qec-lab's
`pipeline/attempts/stab_5_1_3/result.md` for the original formalization log.

The logical basis `X̄ = X⊗⁵`, `Z̄ = Z⊗⁵` is in `FiveQubit_5_1_3Logicals.lean`.

## Outline

- Generators `g1`–`g4` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `stabilizerCode : Code[[5, 1]]`
- Distance 3 (weight-1 and weight-2 anti-witness tables, weight-3 witness):
  `code_has_distance_three`, `stabilizerCodeWithDistance : Code[[5, 1, 3]]`
-/

open NQubitPauliGroupElement

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
theorem GeneratorsIndependent_5_generatorsList : GeneratorsIndependent 5 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-! ## No `−I` in the stabilizer subgroup -/

/-- The closure of the four generators does not contain `−I`. -/
theorem negIdentity_not_mem :
    negIdentity 5 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-! ## Bundled `StabilizerGroup 5` -/

/-- The `[[5, 1, 3]]` stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 5 :=
  mkStabilizerFromGenerators 5 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

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
  closure_no_neg_identity := negIdentity_not_mem

/-- The five-qubit perfect code as a stabilizer code `[[5, 1]]`. -/
noncomputable def stabilizerCode : Code[[5, 1]] := presentation.toCode

/-- The stabilizer code's subgroup is the closure of the generator list. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-! ## Distance 3

### No nontrivial logical of weight 1 or 2

For every weight-1 and weight-2 Pauli, some generator anticommutes with it. Each
case is a closed `Anticommute` statement between literals, decided through the
global `Decidable (Anticommute p q)` instance, with `first` backtracking across
the generators. -/

/-- Every weight-1 Pauli anticommutes with some generator. -/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 5, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ listToSet generatorsList, Anticommute (weightOneAt i P) g := by
  intro i P hP
  fin_cases i <;>
    (match P, hP with
    | PauliOperator.X, _ => first
      | exact ⟨g1, by simp [generatorsList], by decide⟩
      | exact ⟨g2, by simp [generatorsList], by decide⟩
      | exact ⟨g3, by simp [generatorsList], by decide⟩
      | exact ⟨g4, by simp [generatorsList], by decide⟩
    | PauliOperator.Y, _ => first
      | exact ⟨g1, by simp [generatorsList], by decide⟩
      | exact ⟨g2, by simp [generatorsList], by decide⟩
    | PauliOperator.Z, _ => first
      | exact ⟨g1, by simp [generatorsList], by decide⟩
      | exact ⟨g2, by simp [generatorsList], by decide⟩
      | exact ⟨g3, by simp [generatorsList], by decide⟩
    | PauliOperator.I, hP => exact (hP rfl).elim)

/-- Every weight-2 Pauli anticommutes with some generator. The table is the
weight-1 one nested: `match` on `(P, Q)`, then `fin_cases i <;> fin_cases j`,
with `exact absurd rfl hij` discharging the diagonal. Generator branches that
no case of a given `(P, Q)` needs are trimmed (`g4` for `(X, X)`, `(Y, Z)`,
`(Z, Y)`), since an unused `first` alternative trips `linter.unusedTactic`. -/
private lemma weight_two_anticomm_witness :
    ∀ i j : Fin 5, i ≠ j → ∀ P Q : PauliOperator, P ≠ PauliOperator.I →
        Q ≠ PauliOperator.I →
      ∃ g ∈ listToSet generatorsList, Anticommute (weightTwoAt i j P Q) g := by
  intro i j hij P Q hP hQ
  match P, Q, hP, hQ with
  | PauliOperator.I, _, hP, _ => exact (hP rfl).elim
  | _, PauliOperator.I, _, hQ => exact (hQ rfl).elim
  | PauliOperator.X, PauliOperator.X, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
  | PauliOperator.X, PauliOperator.Y, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
        | exact ⟨g4, by simp [generatorsList], by decide⟩
  | PauliOperator.X, PauliOperator.Z, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
        | exact ⟨g4, by simp [generatorsList], by decide⟩
  | PauliOperator.Y, PauliOperator.X, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
        | exact ⟨g4, by simp [generatorsList], by decide⟩
  | PauliOperator.Y, PauliOperator.Y, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
        | exact ⟨g4, by simp [generatorsList], by decide⟩
  | PauliOperator.Y, PauliOperator.Z, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
  | PauliOperator.Z, PauliOperator.X, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
        | exact ⟨g4, by simp [generatorsList], by decide⟩
  | PauliOperator.Z, PauliOperator.Y, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
  | PauliOperator.Z, PauliOperator.Z, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generatorsList], by decide⟩
        | exact ⟨g2, by simp [generatorsList], by decide⟩
        | exact ⟨g3, by simp [generatorsList], by decide⟩
        | exact ⟨g4, by simp [generatorsList], by decide⟩

/-! ### A nontrivial logical of weight 3

`IYYIX` is the operator part of `X⊗⁵ · g1`: it commutes with every generator,
and it anticommutes with `Z⊗⁵` (they clash on qubits 1, 2 and 4), which also
commutes with every generator. -/

/-- `IYYIX`: a nontrivial logical of weight 3. -/
def minWeightLogical : NQubitPauliGroupElement 5 := σ[IYYIX]

/-- `ZZZZZ`: a centralizer element anticommuting with `minWeightLogical`. -/
def minWeightPartner : NQubitPauliGroupElement 5 := σ[ZZZZZ]

lemma minWeightLogical_weight : weight minWeightLogical = 3 := by decide

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

/-- `IYYIX` and `ZZZZZ` anticommute locally on qubits 1, 2 and 4, an odd
number. -/
lemma minWeightLogical_anticommutes_minWeightPartner :
    Anticommute minWeightLogical minWeightPartner := by decide

/-- `IYYIX` is a nontrivial logical operator: it lies in the centralizer and
anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial :
    IsNontrivialLogicalOperator minWeightLogical stabilizerCode.toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ minWeightLogical_mem_centralizer
    minWeightPartner_mem_centralizer minWeightLogical_anticommutes_minWeightPartner

/-! ### The code with its distance `Code[[5, 1, 3]]` -/

/-- **The five-qubit perfect code has distance 3.** The anti-witness tables
rule out nontrivial logicals of weight 1 and 2, and `IYYIX` is a nontrivial
logical of weight 3. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 := by
  refine hasCodeDistance_of stabilizerCode 3 (by decide)
    ⟨minWeightLogical, minWeightLogical_isNontrivial, minWeightLogical_weight⟩ ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  rcases (IsNontrivialLogicalOperator_iff g stabilizerCode.toStabilizerGroup).mp h_nontrivial
    with ⟨h_cent, _⟩
  interval_cases w
  · exact no_weight_one_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup (listToSet generatorsList) stabilizerCode_toSubgroup_eq
      weight_one_anticomm_witness g hg_weight h_cent
  · exact no_weight_two_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup (listToSet generatorsList) stabilizerCode_toSubgroup_eq
      weight_two_anticomm_witness g hg_weight h_cent

/-- The five-qubit perfect code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[5, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three

end FiveQubit_5_1_3
end StabilizerGroup

end Quantum

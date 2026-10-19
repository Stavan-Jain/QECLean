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
namespace CSS_4_1_2

/-!
# The LNCY code `[[4, 1, 2]]`

The Leung–Nielsen–Chuang–Yamamoto code is a four-qubit CSS stabilizer code
encoding one logical qubit, with code distance 2. It detects (but does not
correct) a single arbitrary Pauli error. Originally introduced in
[Leung–Nielsen–Chuang–Yamamoto 1997, `arxiv:quant-ph/9704002`, §II Eqs. 5–6],
with codewords
```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2
|1_L⟩ = (|0011⟩ + |1100⟩)/√2
```
The three generators (`n − k = 3`) are chosen to stabilize these codewords:
`ZZII`, `IIZZ` and `XXXX`. (The EC Zoo entry quotes a *dual* tableau
`(XXII, IIXX, ZZZZ)` from the Qiskit preset; that one stabilizes a different
2-d subspace. We use the LNCY codeword convention as the ground truth.)

The code is packaged by the **decide route**: the three generators form a
literal list, and pairwise commutation, phase zero and check-matrix
independence are closed statements settled by `decide`; `−I ∉ closure` follows
by `negIdentity_not_mem_of_indep_phase_zero_commute`.

Distance 2 is `hasCodeDistance_two_of_anticommute_witness`: every weight-1
Pauli anticommutes with `ZZII` or `IIZZ` (local `X` or `Y`, depending on the
qubit) or with `XXXX` (local `Z`), and `XXII` is a nontrivial logical of
weight 2.

The logical basis `X̄ = XXII`, `Z̄ = ZIZI` is in `CSS_4_1_2Logicals.lean`.

## Outline

- Generators `Z1`, `Z2`, `X1` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `stabilizerCode : Code[[4, 1]]`
- Distance 2 (weight-1 anti-witness table, weight-2 witness):
  `code_has_distance_two`, `stabilizerCodeWithDistance : Code[[4, 1, 2]]`
-/

open NQubitPauliGroupElement

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

/-! ## Decided hypotheses

`ZZII` meets `XXXX` on qubits 0 and 1 and `IIZZ` meets it on qubits 2 and 3 —
both even, so all pairs commute. `decide` checks the nine ordered pairs, the
phases, and the check-matrix rank. -/

/-- All three generators pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the three generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_4_generatorsList : GeneratorsIndependent 4 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-! ## No `−I` in the stabilizer subgroup -/

/-- The closure of the three generators does not contain `−I`. -/
theorem negIdentity_not_mem :
    negIdentity 4 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-! ## Bundled `StabilizerGroup 4` -/

/-- The `[[4, 1, 2]]` stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 4 :=
  mkStabilizerFromGenerators 4 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-! ## The bare code `Code[[4, 1]]`

Three independent, pairwise commuting generators on four qubits: one logical
qubit. -/

/-- The generator list as a presentation of a `[[4, 1]]` code: its 3
check-matrix rows are linearly independent. -/
def presentation : StabilizerCode.Presentation 4 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := rowsLinearIndependent_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- The LNCY code as a stabilizer code `[[4, 1]]`. -/
noncomputable def stabilizerCode : Code[[4, 1]] := presentation.toCode

/-- The stabilizer code's subgroup is the closure of the generator list. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-! ## Distance 2

### No nontrivial logical of weight 1

A local `X` or `Y` anticommutes with the `Z` of `ZZII` on qubits 0, 1 and with
the `Z` of `IIZZ` on qubits 2, 3; a local `Z` anticommutes with the `X` of
`XXXX` on every qubit. `first` picks whichever Z-check covers the qubit. -/

/-- Every weight-1 Pauli anticommutes with some generator. -/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 4, ∀ P : PauliOperator, P ≠ PauliOperator.I →
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
    | PauliOperator.Z, _ => exact ⟨X1, by simp [generatorsList], by decide⟩
    | PauliOperator.I, hP => exact (hP rfl).elim)

/-! ### A nontrivial logical of weight 2

`XXII` meets `ZZII` on two qubits and `IIZZ` on none, so it commutes with every
check; it anticommutes with `ZIZI` (one shared qubit), which meets `XXXX` on two
qubits and so also commutes with every check. -/

/-- `XXII`: a nontrivial logical of weight 2. -/
def minWeightLogical : NQubitPauliGroupElement 4 := σ[XXII]

/-- `ZIZI`: a centralizer element anticommuting with `minWeightLogical`. -/
def minWeightPartner : NQubitPauliGroupElement 4 := σ[ZIZI]

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

/-- `XXII` and `ZIZI` meet on qubit 0 only, an odd number. -/
lemma minWeightLogical_anticommutes_minWeightPartner :
    Anticommute minWeightLogical minWeightPartner := by decide

/-- `XXII` is a nontrivial logical operator: it lies in the centralizer and
anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial :
    IsNontrivialLogicalOperator minWeightLogical stabilizerCode.toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ minWeightLogical_mem_centralizer
    minWeightPartner_mem_centralizer minWeightLogical_anticommutes_minWeightPartner

/-! ### The code with its distance `Code[[4, 1, 2]]` -/

/-- **The LNCY code has distance 2.** Every weight-1 Pauli anticommutes with
some generator, and `XXII` is a nontrivial logical of weight 2. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode (listToSet generatorsList)
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨minWeightLogical, minWeightLogical_isNontrivial, minWeightLogical_weight⟩

/-- The LNCY code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[4, 1, 2]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_two

end CSS_4_1_2
end StabilizerGroup

end Quantum

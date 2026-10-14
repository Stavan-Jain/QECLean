import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace RepetitionCode3

/-!
# The 3-qubit repetition code `[[3, 1, 1]]`

The classical bit-flip repetition code, embedded as a quantum stabilizer code:
two `Z`-checks, `ZZ` on adjacent qubits, and no `X`-checks. It encodes one
logical qubit.

The code is packaged by the **decide route**: the two generators form a literal
list, and pairwise commutation, phase zero and check-matrix independence are
closed statements settled by `decide`; `−I ∉ closure` follows by
`negIdentity_not_mem_of_indep_phase_zero_commute`.

As a *quantum* code it has distance 1: it protects against bit flips only. A
single phase flip `Z` on qubit 0 commutes with both checks, yet it is not a
stabilizer, since it anticommutes with `XXX`, which also commutes with both.

The logical basis `X̄ = XXX`, `Z̄ = ZZZ` is in `ThreeLogicals.lean`.

## Outline

- Generators `Z1`, `Z2` and the list `generatorsList`
- Decided hypotheses: `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList`
- `negIdentity_not_mem`, the bundled `stabilizerGroup`
- `stabilizerCode : Code[[3, 1]]`
- Distance 1 (weight-1 witness): `code_has_distance_one`,
  `stabilizerCodeWithDistance : Code[[3, 1, 1]]`
-/

open NQubitPauliGroupElement

/-! ## Generators -/

/-- First Z-check: `ZZI` (Z on qubits 0, 1). -/
def Z1 : NQubitPauliGroupElement 3 := σ[ZZI]

/-- Second Z-check: `IZZ` (Z on qubits 1, 2). -/
def Z2 : NQubitPauliGroupElement 3 := σ[IZZ]

/-- The two generators as a list. -/
def generatorsList : List (NQubitPauliGroupElement 3) :=
  [Z1, Z2]

/-! ## Decided hypotheses

Both generators are Z-type, so they commute componentwise. `decide` checks the
four ordered pairs, the phases, and the check-matrix rank. -/

/-- The two generators commute. -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- Every generator has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the two generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_3_generatorsList : GeneratorsIndependent 3 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-! ## No `−I` in the stabilizer subgroup -/

/-- The closure of the two generators does not contain `−I`. -/
theorem negIdentity_not_mem :
    negIdentity 3 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-! ## Bundled `StabilizerGroup 3` -/

/-- The 3-qubit repetition stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 3 :=
  mkStabilizerFromGenerators 3 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-! ## The bare code `Code[[3, 1]]`

Two independent, commuting generators on three qubits: one logical qubit. -/

/-- The 3-qubit repetition code as a stabilizer code `[[3, 1]]`. -/
noncomputable def stabilizerCode : Code[[3, 1]] where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_3_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- The stabilizer code's subgroup is the closure of the generator list. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) :=
  rfl

/-! ## Distance 1

Every nontrivial logical of positive weight trivially has weight at least 1,
so there is no lower bound to prove: only a weight-1 witness.

### A nontrivial logical of weight 1

`Z` on qubit 0 commutes with both checks (all three operators are Z-type), and
it anticommutes with `XXX` (one shared qubit), which meets each check on two
qubits and so also commutes with both. -/

/-- `ZII`: a nontrivial logical of weight 1. -/
def minWeightLogical : NQubitPauliGroupElement 3 := σ[ZII]

/-- `XXX`: a centralizer element anticommuting with `minWeightLogical`. -/
def minWeightPartner : NQubitPauliGroupElement 3 := σ[XXX]

lemma minWeightLogical_weight : weight minWeightLogical = 1 := by decide

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

/-- `ZII` and `XXX` meet on qubit 0 only, an odd number. -/
lemma minWeightLogical_anticommutes_minWeightPartner :
    Anticommute minWeightLogical minWeightPartner := by decide

/-- `Z` on qubit 0 is a nontrivial logical operator: it lies in the centralizer
and anticommutes with the centralizer element `minWeightPartner`. -/
lemma minWeightLogical_isNontrivial :
    IsNontrivialLogicalOperator minWeightLogical stabilizerCode.toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ minWeightLogical_mem_centralizer
    minWeightPartner_mem_centralizer minWeightLogical_anticommutes_minWeightPartner

/-! ### The code with its distance `Code[[3, 1, 1]]` -/

/-- **The 3-qubit repetition code has distance 1.** Every nontrivial logical of
positive weight has weight at least 1, and `Z` on qubit 0 attains it. -/
theorem code_has_distance_one : HasCodeDistance stabilizerCode 1 :=
  ⟨le_rfl, fun _ _ hw => hw, minWeightLogical, minWeightLogical_isNontrivial,
    minWeightLogical_weight⟩

/-- The 3-qubit repetition code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[3, 1, 1]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_one

end RepetitionCode3
end StabilizerGroup

end Quantum

import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace RepetitionCode3

/-!
# The 3-qubit repetition code (Z-stabilizer only)

Stabilizer generators: Z₁Z₂ and Z₂Z₃ (Z on adjacent pairs). The code encodes one
logical qubit; logical X = X₁X₂X₃, logical Z = Z₁Z₂Z₃.

The code is packaged by the **decide route**: the two generators form a literal
list, and pairwise commutation, phase zero and check-matrix independence are
closed statements settled by `decide`; `−I ∉ closure` follows by
`negIdentity_not_mem_of_indep_phase_zero_commute`.

## Outline

- Generators `Z1Z2`, `Z2Z3` and the list `generatorsList`
- Decided hypotheses and `negIdentity_not_mem`; the bundled `stabilizerGroup`
- Logical operators `X̄ = XXX`, `Z̄ = ZZZ`
- `stabilizerCode : StabilizerCode 3 1` and `stabilizerCodeWithLogicals`
- Distance 1: `Z` on a single qubit is a nontrivial logical
-/

open NQubitPauliGroupElement

/-- Z₁Z₂: Z on qubits 0 and 1, I on qubit 2. -/
def Z1Z2 : NQubitPauliGroupElement 3 := σ[ZZI]

/-- Z₂Z₃: I on qubit 0, Z on qubits 1 and 2. -/
def Z2Z3 : NQubitPauliGroupElement 3 := σ[IZZ]

/-- The two generators as a list. -/
def generatorsList : List (NQubitPauliGroupElement 3) :=
  [Z1Z2, Z2Z3]

/-!
## Decided hypotheses
-/

/-- The generators pairwise commute (both are Z-type). -/
theorem generators_commute :
    ∀ g ∈ listToSet generatorsList, ∀ h ∈ listToSet generatorsList, g * h = h * g := by
  decide

/-- Every element of the generators list has phase power 0. -/
lemma AllPhaseZero_generatorsList : AllPhaseZero generatorsList := by
  decide

/-- The check-matrix rows of the repetition-code generators are linearly
independent. -/
theorem rowsLinearIndependent_generatorsList :
    rowsLinearIndependent generatorsList := by decide

/-- The repetition-code generator list is an independent generating set. -/
theorem GeneratorsIndependent_3_generatorsList : GeneratorsIndependent 3 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent rowsLinearIndependent_generatorsList

/-!
## No `-I` in the generated subgroup, and the bundled `StabilizerGroup 3`
-/

/-- The closure of the two generators does not contain −I. -/
lemma negIdentity_not_mem :
    negIdentity 3 ∉ Subgroup.closure (listToSet generatorsList) :=
  negIdentity_not_mem_of_indep_phase_zero_commute generatorsList
    AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList generators_commute

/-- The 3-qubit repetition code as a stabilizer group (canonical: from generator
list). -/
noncomputable def stabilizerGroup : StabilizerGroup 3 :=
  mkStabilizerFromGenerators 3 generatorsList generators_commute negIdentity_not_mem

/-- The stabilizer subgroup is the closure of the generator list. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = Subgroup.closure (listToSet generatorsList) := rfl

/-!
## Logical operators
-/

/-- Logical X: X on all three qubits (X₁X₂X₃). -/
def logicalX : NQubitPauliGroupElement 3 :=
  ⟨0, NQubitPauliOperator.X 3⟩

/-- Logical Z: Z on all three qubits (Z₁Z₂Z₃). -/
def logicalZ : NQubitPauliGroupElement 3 :=
  ⟨0, NQubitPauliOperator.Z 3⟩

/-- Logical X and logical Z anticommute: X₁X₂X₃ and Z₁Z₂Z₃ anticommute at every
qubit. -/
theorem logicalX_anticommutes_logicalZ : NQubitPauliGroupElement.Anticommute logicalX logicalZ :=
  NQubitPauliOperator.allX_allZ_anticommute 3 (by decide)

private lemma logicalX_commutes_Z1Z2 : logicalX * Z1Z2 = Z1Z2 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 3) logicalX.operators Z1Z2.operators)) =
        ({0, 1} : Finset (Fin 3)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, Z1Z2,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  simp [hfilter]

private lemma logicalX_commutes_Z2Z3 : logicalX * Z2Z3 = Z2Z3 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 3) logicalX.operators Z2Z3.operators)) =
        ({1, 2} : Finset (Fin 3)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, Z2Z3,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  simp [hfilter]

/-- Logical X commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl
  · exact logicalX_commutes_Z1Z2.symm
  · exact logicalX_commutes_Z2Z3.symm

/-- Logical X is X-type (X on every qubit). -/
lemma logicalX_is_XType : NQubitPauliGroupElement.IsXTypeElement logicalX := by
  constructor
  · rfl
  · intro i
    fin_cases i <;> simp [logicalX, NQubitPauliOperator.X, PauliOperator.IsXType]

private lemma logicalZ_commutes_Z1Z2 : logicalZ * Z1Z2 = Z1Z2 * logicalZ := by
  pauli_comm_componentwise [logicalZ, Z1Z2]
  all_goals simp only [NQubitPauliOperator.Z]

private lemma logicalZ_commutes_Z2Z3 : logicalZ * Z2Z3 = Z2Z3 * logicalZ := by
  pauli_comm_componentwise [logicalZ, Z2Z3]
  all_goals simp only [NQubitPauliOperator.Z]

/-- Logical Z commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl
  · exact logicalZ_commutes_Z1Z2.symm
  · exact logicalZ_commutes_Z2Z3.symm

/-!
## StabilizerCode [[3, 1]]
-/

private def logicalOpsRep3 : Fin 1 → LogicalQubitOps 3 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩

/-- The 3-qubit repetition code as a stabilizer code [[3, 1]]: one logical
qubit. -/
noncomputable def stabilizerCode : StabilizerCode 3 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_3_generatorsList
  generators_commute := generators_commute
  closure_no_neg_identity := negIdentity_not_mem

/-- The 3-qubit repetition code packaged with its logical pair
`(logicalX, logicalZ)`. -/
noncomputable def stabilizerCodeWithLogicals : StabilizerCodeWithLogicals 3 1 where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOpsRep3
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

/-!
## Code distance [[3, 1, 1]]

The repetition code has distance 1: a single Z on any physical qubit is a
nontrivial logical (same coset as logical Z). So the minimum weight of a
nontrivial logical is 1.
-/

open NQubitPauliOperator NQubitPauliGroupElement

/-- Z on qubit 2 only (I on qubits 0 and 1). -/
def Z_on_qubit2 : NQubitPauliGroupElement 3 := σ[IIZ]

lemma Z_on_qubit2_operators (i : Fin 3) :
    Z_on_qubit2.operators i = if i = 2 then PauliOperator.Z else PauliOperator.I := by
  simp only [Z_on_qubit2, NQubitPauliOperator.set, NQubitPauliOperator.identity]

/-- Z_on_qubit2 has weight 1. -/
lemma weight_Z_on_qubit2 : NQubitPauliGroupElement.weight Z_on_qubit2 = 1 := by
  have h : NQubitPauliOperator.support Z_on_qubit2.operators = {2} := by
    ext i
    simp only [NQubitPauliOperator.mem_support, Z_on_qubit2_operators, Finset.mem_singleton]
    split_ifs with h <;> simp [h]
  rw [NQubitPauliGroupElement.weight, NQubitPauliOperator.weight, h]
  simp only [Finset.card_singleton]

private lemma Z_on_qubit2_commutes_Z1Z2 : Z_on_qubit2 * Z1Z2 = Z1Z2 * Z_on_qubit2 := by
  pauli_comm_componentwise [Z_on_qubit2, Z1Z2]

private lemma Z_on_qubit2_commutes_Z2Z3 : Z_on_qubit2 * Z2Z3 = Z2Z3 * Z_on_qubit2 := by
  pauli_comm_componentwise [Z_on_qubit2, Z2Z3]

/-- Z_on_qubit2 is in the centralizer of the repetition-code stabilizer. -/
lemma Z_on_qubit2_mem_centralizer : Z_on_qubit2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false] at hs
  rcases hs with rfl | rfl
  · exact Z_on_qubit2_commutes_Z1Z2.symm
  · exact Z_on_qubit2_commutes_Z2Z3.symm

/-- Z_on_qubit2 anticommutes with logical X (overlap only on qubit 2, where X
and Z anticommute). -/
lemma Z_on_qubit2_anticommutes_logicalX :
    NQubitPauliGroupElement.Anticommute Z_on_qubit2 logicalX := by
  classical
  rw [NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes]
  have hfilter :
      (Finset.univ.filter
          (NQubitPauliGroupElement.anticommutesAt (n := 3) Z_on_qubit2.operators
            logicalX.operators)) = ({2} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, Z_on_qubit2_operators,
        logicalX, NQubitPauliOperator.X, PauliOperator.mulOp]
  rw [hfilter]
  decide

/-- Z_on_qubit2 is not in the stabilizer: it anticommutes with logical X (in the
centralizer). -/
lemma Z_on_qubit2_not_mem_subgroup : Z_on_qubit2 ∉ stabilizerGroup.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer stabilizerGroup Z_on_qubit2 logicalX
    logicalX_mem_centralizer Z_on_qubit2_anticommutes_logicalX

/-- No stabilizer element has the same operator part as Z_on_qubit2 (stabilizers
are products of adjacent Zs; Z_on_qubit2 is Z on one qubit only). -/
lemma Z_on_qubit2_operators_ne_of_mem (s : NQubitPauliGroupElement 3)
    (hs : s ∈ stabilizerGroup.toSubgroup) :
    s.operators ≠ Z_on_qubit2.operators := by
      by_contra h_eq;
      have h_contradiction :
          NQubitPauliOperator.toSymplectic s.operators ∈
            NQubitPauliGroupElement.sympSpan generatorsList :=
        mem_closure_implies_symp_in_span generatorsList AllPhaseZero_generatorsList s hs
      simp_all +decide [ NQubitPauliGroupElement.sympSpan ];
      rw [ Submodule.mem_span_range_iff_exists_fun ] at h_contradiction;
      obtain ⟨ c, hc ⟩ := h_contradiction;
      fin_cases c <;> simp_all +decide

/-- Z_on_qubit2 is a nontrivial logical operator of weight 1. -/
lemma Z_on_qubit2_nontrivial_logical :
    IsNontrivialLogicalOperator Z_on_qubit2 stabilizerGroup :=
  ⟨Z_on_qubit2_mem_centralizer, fun s hs => Z_on_qubit2_operators_ne_of_mem s hs⟩

/-- The 3-qubit repetition code has code distance 1. -/
theorem repetitionCode3_has_distance_one : HasCodeDistance stabilizerCode 1 := by
  refine ⟨by decide, ?_, ⟨Z_on_qubit2, Z_on_qubit2_nontrivial_logical, weight_Z_on_qubit2⟩⟩
  intro g _ hw
  exact Nat.one_le_of_lt hw

/-- The minimum weight of a nontrivial logical operator for the repetition code
is 1. -/
theorem repetitionCode3_min_weight_nontrivial_logical (g : NQubitPauliGroupElement 3)
    (hg : IsNontrivialLogicalOperator g stabilizerGroup)
    (hw : 0 < NQubitPauliGroupElement.weight g) :
    NQubitPauliGroupElement.weight g ≥ 1 :=
  HasCodeDistance.min_weight stabilizerCode 1 repetitionCode3_has_distance_one g hg hw

/-- The 3-qubit repetition code as a `[[3, 1, 1]]` stabilizer code with
distance. -/
noncomputable def stabilizerCodeWithDistance : StabilizerCodeWithDistance 3 1 1 where
  toStabilizerCode := stabilizerCode
  hasDistance      := repetitionCode3_has_distance_one

end RepetitionCode3
end StabilizerGroup

end Quantum

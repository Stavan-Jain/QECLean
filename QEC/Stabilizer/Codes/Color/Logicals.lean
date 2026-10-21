import QEC.Stabilizer.Codes.Color.Code
import QEC.Stabilizer.Framework.Homological.Distance

/-!
# Transversal logical operators of the triangular color code

Applying X or Z to every physical qubit commutes with every face check,
because face supports have even size. These two operators anticommute,
because the patch has an odd number of physical qubits. They give the
single logical qubit of the canonical color-code stabilizer.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological
open NQubitPauliGroupElement

/-- The chain supported on every physical site. -/
def allOnes (r : ℕ) : Qubit r → ZMod 2 := fun _ => 1

/-- Every face incidence row has even parity. -/
theorem incidence_sum_zero {r : ℕ} (f : Face r) :
    ∑ q, incidence f q = 0 := by
  have h (q : Qubit r) : incidence f q * incidence f q = incidence f q := by
    unfold incidence
    split_ifs <;> norm_num
  simpa only [h] using incidence_orthogonal f f

/-- The all-ones chain has zero syndrome. -/
theorem allOnes_mem_cycles (r : ℕ) : allOnes r ∈ (homologicalCode r).cycles := by
  change (homologicalCode r).boundary1 (allOnes r) = 0
  ext f
  change (∑ q, incidence f q * 1) = 0
  simpa only [_root_.mul_one] using incidence_sum_zero f

/-- The all-ones chain is also a dual cycle. -/
theorem allOnes_mem_dualCycles (r : ℕ) :
    allOnes r ∈ (homologicalCode r).dualCycles := by
  rw [dualCycles_eq_cycles]
  exact allOnes_mem_cycles r

/-- The all-ones chain has odd self-pairing. -/
theorem allOnes_innerProduct (r : ℕ) :
    (homologicalCode r).chainInnerProduct (allOnes r) (allOnes r) = 1 := by
  change (∑ _q : Qubit r, (1 : ZMod 2) * 1) = 1
  simp only [_root_.mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_qubit, ← twice_numFaces]
  simp [show (2 : ZMod 2) = 0 from rfl]

/-- Logical X applies X at every physical site. -/
noncomputable def logicalX (r : ℕ) : NQubitPauliGroupElement (numQubits r) :=
  (homologicalCode r).chainXOperator (allOnes r)

/-- Logical Z applies Z at every physical site. -/
noncomputable def logicalZ (r : ℕ) : NQubitPauliGroupElement (numQubits r) :=
  (homologicalCode r).chainZOperator (allOnes r)

/-- Transversal X commutes with every stabilizer. -/
theorem logicalX_mem_centralizer (r : ℕ) :
    logicalX r ∈ centralizer (stabilizerGroup r) := by
  rw [centralizer_eq_of_toSubgroup_eq _ _ (stabilizerGroup_eq_homological_subgroup r)]
  exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles
    (X := homologicalCode r) (allOnes r)).mpr (allOnes_mem_cycles r)

/-- Transversal Z commutes with every stabilizer. -/
theorem logicalZ_mem_centralizer (r : ℕ) :
    logicalZ r ∈ centralizer (stabilizerGroup r) := by
  rw [centralizer_eq_of_toSubgroup_eq _ _ (stabilizerGroup_eq_homological_subgroup r)]
  exact (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles
    (X := homologicalCode r) (allOnes r)).mpr (allOnes_mem_dualCycles r)

/-- The transversal X and Z logical operators anticommute. -/
theorem logicalX_anticommutes_logicalZ (r : ℕ) :
    Anticommute (logicalX r) (logicalZ r) := by
  rcases commute_or_anticommute (logicalX r) (logicalZ r) with hc | ha
  · have hzero := (HomologicalCode.chainXOperator_commutes_chainZOperator_iff
      (X := homologicalCode r) (allOnes r) (allOnes r)).mp hc
    rw [allOnes_innerProduct] at hzero
    exact (one_ne_zero hzero).elim
  · exact ha

/-- The single logical qubit of the triangular color code. -/
noncomputable def logicalOps (r : ℕ) : Fin 1 → LogicalQubitOps (numQubits r)
    (stabilizerGroup r) := fun _ =>
  ⟨logicalX r, logicalZ r, logicalX_mem_centralizer r, logicalZ_mem_centralizer r,
    logicalX_anticommutes_logicalZ r⟩

/-- The parametric color code with its transversal logical basis. -/
noncomputable def stabilizerCodeWithLogicals (r : ℕ) :
    StabilizerCodeWithLogicals (numQubits r) 1 where
  toStabilizerCode := stabilizerCode r
  logicalOps := logicalOps r
  logical_commute_cross := fun i j h => (h (Subsingleton.elim i j)).elim

/-- Transversal X is a nontrivial logical operator of the canonical code. -/
theorem logicalX_nontrivial (r : ℕ) :
    IsNontrivialLogicalOperator (logicalX r) (stabilizerGroup r) :=
  (logicalOps r 0).xOp_nontrivial

/-- Transversal Z is a nontrivial logical operator of the canonical code. -/
theorem logicalZ_nontrivial (r : ℕ) :
    IsNontrivialLogicalOperator (logicalZ r) (stabilizerGroup r) :=
  (logicalOps r 0).zOp_nontrivial

/-- The transversal X logical has support on every physical qubit. -/
theorem logicalX_weight (r : ℕ) : weight (logicalX r) = numQubits r := by
  change weight ((homologicalCode r).chainXOperator (allOnes r)) = _
  rw [HomologicalCode.weight_chainXOperator (X := homologicalCode r)]
  change (Finset.univ.filter fun _q : Qubit r => (1 : ZMod 2) ≠ 0).card = _
  simpa only [ne_eq, one_ne_zero, not_false_eq_true, Finset.filter_true,
    Finset.card_univ] using card_qubit r

/-- The transversal Z logical has support on every physical qubit. -/
theorem logicalZ_weight (r : ℕ) : weight (logicalZ r) = numQubits r := by
  change weight ((homologicalCode r).chainZOperator (allOnes r)) = _
  rw [HomologicalCode.weight_chainZOperator (X := homologicalCode r)]
  change (Finset.univ.filter fun _q : Qubit r => (1 : ZMod 2) ≠ 0).card = _
  simpa only [ne_eq, one_ne_zero, not_false_eq_true, Finset.filter_true,
    Finset.card_univ] using card_qubit r

end Quantum.StabilizerGroup.ColorCode

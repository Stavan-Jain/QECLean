import QEC.Stabilizer.Codes.Color.Code
import QEC.Stabilizer.Framework.Homological.Distance

/-!
# Transversal logical operators of the triangular color code

The all-ones chain `allOnes r` is a cycle, because every face has an even
number of qubits (`allOnes_mem_cycles`), and it pairs to `1` with itself,
because the number of qubits is odd (`allOnes_innerProduct`). Hence the
operators `logicalX r` and `logicalZ r`, which apply `X` and `Z` to every
qubit, commute with the stabilizer group (`logicalX_mem_centralizer`,
`logicalZ_mem_centralizer`) and anticommute with each other
(`logicalX_anticommutes_logicalZ`). They are the logical operators of the one
logical qubit of the code, packaged as `stabilizerCodeWithLogicals r`, and
have weight `numQubits r` (`logicalX_weight`, `logicalZ_weight`).
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological
open NQubitPauliGroupElement

/-- The chain supported on every qubit. -/
def allOnes (r : ℕ) : Qubit r → ZMod 2 := fun _ => 1

/-- The all-ones chain is a cycle: every face has an even number of
qubits. -/
lemma allOnes_mem_cycles (r : ℕ) : allOnes r ∈ (homologicalCode r).cycles :=
  (mem_cycles_iff_sum_faceSupport _).mpr faceSupport_sum_one

/-- The all-ones chain is a dual cycle. -/
lemma allOnes_mem_dualCycles (r : ℕ) :
    allOnes r ∈ (homologicalCode r).dualCycles :=
  (dualCycles_eq_cycles r).symm ▸ allOnes_mem_cycles r

/-- The all-ones chain has odd parity: the number of qubits is odd. -/
lemma allOnes_sum_one (r : ℕ) : ∑ q, allOnes r q = 1 := by
  simp only [allOnes, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, _root_.mul_one,
    ZMod.natCast_eq_one_iff_odd]
  exact ⟨_, card_qubit_eq_two_mul_card_face_add_one r⟩

/-- The all-ones chain pairs to `1` with itself. -/
lemma allOnes_innerProduct (r : ℕ) :
    (homologicalCode r).chainInnerProduct (allOnes r) (allOnes r) = 1 := by
  simpa only [HomologicalCode.chainInnerProduct, allOnes, _root_.mul_one] using
    allOnes_sum_one r

/-- The all-ones chain has weight `numQubits r`. -/
lemma allOnes_weight (r : ℕ) :
    (homologicalCode r).chainWeight (allOnes r) = numQubits r := by
  have h : (homologicalCode r).chainSupport (allOnes r) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => one_ne_zero
  rw [HomologicalCode.chainWeight, h]
  exact card_qubit r

/-- The logical X operator: `X` on every qubit. -/
noncomputable def logicalX (r : ℕ) : NQubitPauliGroupElement (numQubits r) :=
  (homologicalCode r).chainXOperator (allOnes r)

/-- The logical Z operator: `Z` on every qubit. -/
noncomputable def logicalZ (r : ℕ) : NQubitPauliGroupElement (numQubits r) :=
  (homologicalCode r).chainZOperator (allOnes r)

/-- The logical X operator commutes with every stabilizer. -/
theorem logicalX_mem_centralizer (r : ℕ) :
    logicalX r ∈ centralizer (stabilizerGroup r) := by
  rw [centralizer_eq_of_toSubgroup_eq _ _ (stabilizerGroup_eq_homological_subgroup r)]
  exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles
    (X := homologicalCode r) (allOnes r)).mpr (allOnes_mem_cycles r)

/-- The logical Z operator commutes with every stabilizer. -/
theorem logicalZ_mem_centralizer (r : ℕ) :
    logicalZ r ∈ centralizer (stabilizerGroup r) := by
  rw [centralizer_eq_of_toSubgroup_eq _ _ (stabilizerGroup_eq_homological_subgroup r)]
  exact (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles
    (X := homologicalCode r) (allOnes r)).mpr (allOnes_mem_dualCycles r)

/-- The logical X and Z operators anticommute, because the all-ones chain
pairs to `1` with itself. -/
theorem logicalX_anticommutes_logicalZ (r : ℕ) :
    Anticommute (logicalX r) (logicalZ r) :=
  (commute_or_anticommute _ _).resolve_left fun hc => one_ne_zero <|
    (allOnes_innerProduct r).symm.trans <|
      (HomologicalCode.chainXOperator_commutes_chainZOperator_iff
        (X := homologicalCode r) _ _).mp hc

/-- The logical operators of the one logical qubit of the color code. -/
noncomputable def logicalOps (r : ℕ) : Fin 1 → LogicalQubitOps (numQubits r)
    (stabilizerGroup r) := fun _ =>
  ⟨logicalX r, logicalZ r, logicalX_mem_centralizer r, logicalZ_mem_centralizer r,
    logicalX_anticommutes_logicalZ r⟩

/-- The triangular color code together with its transversal logical X and Z
operators. -/
noncomputable def stabilizerCodeWithLogicals (r : ℕ) :
    StabilizerCodeWithLogicals (numQubits r) 1 where
  toStabilizerCode := stabilizerCode r
  logicalOps := logicalOps r
  logical_commute_cross := fun i j h => (h (Subsingleton.elim i j)).elim

/-- The logical X operator is a nontrivial logical operator. -/
theorem logicalX_nontrivial (r : ℕ) :
    IsNontrivialLogicalOperator (logicalX r) (stabilizerGroup r) :=
  (logicalOps r 0).xOp_nontrivial

/-- The logical Z operator is a nontrivial logical operator. -/
theorem logicalZ_nontrivial (r : ℕ) :
    IsNontrivialLogicalOperator (logicalZ r) (stabilizerGroup r) :=
  (logicalOps r 0).zOp_nontrivial

/-- The logical X operator is supported on every qubit. -/
theorem logicalX_weight (r : ℕ) : weight (logicalX r) = numQubits r :=
  (HomologicalCode.weight_chainXOperator (X := homologicalCode r) _).trans (allOnes_weight r)

/-- The logical Z operator is supported on every qubit. -/
theorem logicalZ_weight (r : ℕ) : weight (logicalZ r) = numQubits r :=
  (HomologicalCode.weight_chainZOperator (X := homologicalCode r) _).trans (allOnes_weight r)

end Quantum.StabilizerGroup.ColorCode

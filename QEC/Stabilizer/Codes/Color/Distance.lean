import QEC.Stabilizer.Codes.Color.Boundary
import QEC.Stabilizer.Codes.Color.LowerBound

/-!
# The parameters of the triangular honeycomb color code

The binary lower bound and a left-boundary logical establish distance
`2r+1`. The CSS distance bridge includes arbitrary mixed Pauli operators.
Together with the independent face checks, this packages the family as
`[[3r(r+1)+1, 1, 2r+1]]`, or `[[ (3d²+1)/4, 1, d ]]` for odd `d`.
-/

namespace Quantum.StabilizerGroup.ColorCode

open Stabilizer.Homological
open NQubitPauliGroupElement

/-- Every nontrivial binary logical class has weight at least `2r+1`. -/
theorem nontrivial_cycle_weight_lower_bound {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles)
    (hnb : c ∉ (homologicalCode r).boundaries) :
    distance r ≤ (homologicalCode r).chainWeight c :=
  odd_cycle_weight_lower_bound c hc ((cycle_not_mem_boundaries_iff_odd c hc).mp hnb)

/-- Every nontrivial Pauli logical, including mixed X/Z operators, has
weight at least `2r+1`. -/
theorem logical_weight_lower_bound {r : ℕ}
    (g : NQubitPauliGroupElement (numQubits r))
    (hg : IsNontrivialLogicalOperator g (stabilizerGroup r)) :
    distance r ≤ weight g := by
  have hhom := (IsNontrivialLogicalOperator_of_toSubgroup_eq g
    (stabilizerGroup_eq_homological_subgroup r)).mp hg
  apply HomologicalCode.chainWeight_lower_bound_transfers (homologicalCode r)
    (distance r) ?_ ?_ g hhom
  · exact fun c hc hnb => nontrivial_cycle_weight_lower_bound c hc hnb
  · rw [dualCycles_eq_cycles, dualBoundaries_eq_boundaries]
    exact fun c hc hnb => nontrivial_cycle_weight_lower_bound c hc hnb

/-- The left-boundary X operator attains the distance of the canonical code. -/
theorem exists_logical_weight_eq_distance (r : ℕ) :
    ∃ g, IsNontrivialLogicalOperator g (stabilizerGroup r) ∧ weight g = distance r := by
  refine ⟨(homologicalCode r).chainXOperator (leftBoundary r), ?_, ?_⟩
  · apply (IsNontrivialLogicalOperator_of_toSubgroup_eq _
      (stabilizerGroup_eq_homological_subgroup r)).mpr
    exact (HomologicalCode.chainXOperator_isNontrivialLogical_iff
      (X := homologicalCode r) (leftBoundary r)).mpr
      ⟨leftBoundary_mem_cycles r, leftBoundary_not_mem_boundaries r⟩
  · exact (HomologicalCode.weight_chainXOperator
      (X := homologicalCode r) (leftBoundary r)).trans (leftBoundary_weight r)

/-- The triangular honeycomb color code has distance exactly `2r+1`. -/
theorem has_code_distance (r : ℕ) :
    HasCodeDistance (stabilizerCode r) (distance r) := by
  refine ⟨by unfold distance; omega, ?_, exists_logical_weight_eq_distance r⟩
  exact fun g hg _ => logical_weight_lower_bound g hg

/-- The triangular color code with all three parameters proved. -/
noncomputable def stabilizerCodeWithDistance (r : ℕ) :
    StabilizerCodeWithDistance (numQubits r) 1 (distance r) where
  toStabilizerCode := stabilizerCode r
  hasDistance := has_code_distance r

/-- The paper's `[[ (3d²+1)/4, 1, d ]]` family, indexed by odd distance. -/
noncomputable def codeOfOddDistance (d : ℕ) (hodd : Odd d) :
    StabilizerCodeWithDistance ((3 * d ^ 2 + 1) / 4) 1 d := by
  have hd : distance (d / 2) = d := by
    obtain ⟨r, hr⟩ := hodd
    unfold distance
    omega
  have hn : numQubits (d / 2) = (3 * d ^ 2 + 1) / 4 := by
    rw [numQubits_eq_distance, hd]
  simpa only [hn, hd] using stabilizerCodeWithDistance (d / 2)

end Quantum.StabilizerGroup.ColorCode

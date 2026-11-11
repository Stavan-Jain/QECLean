import QEC.Stabilizer.Codes.Color.Boundary
import QEC.Stabilizer.Codes.Color.LowerBound

/-!
# The distance of the triangular color code

The color code of parameter `r` has distance `distance r = 2 * r + 1`
(`has_code_distance`). The lower bound holds for every nontrivial logical
operator, of any Pauli type (`logical_weight_lower_bound`): its X-support
chain or its Z-support chain is a cycle that is not a boundary, hence a cycle
of odd parity, of weight at least `2 * r + 1`. The bound is attained by the
X-chain operator of the left side of the patch
(`exists_logical_weight_eq_distance`).

`stabilizerCodeWithDistance r` packages the code with its parameters
`[[3r(r+1) + 1, 1, 2r + 1]]`, and `codeOfOddDistance d` states them in terms of
an odd distance `d` as `[[(3d² + 1)/4, 1, d]]`.
-/

namespace Quantum.StabilizerGroup.ColorCode

open Stabilizer.Homological
open NQubitPauliGroupElement

/-- Every cycle that is not a boundary has weight at least `2 * r + 1`. -/
lemma nontrivial_cycle_weight_lower_bound {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles)
    (hnb : c ∉ (homologicalCode r).boundaries) :
    distance r ≤ (homologicalCode r).chainWeight c :=
  odd_cycle_weight_lower_bound c hc ((cycle_not_mem_boundaries_iff_odd c hc).mp hnb)

/-- Every nontrivial logical operator of the color code, of any Pauli type,
has weight at least `2 * r + 1`. -/
theorem logical_weight_lower_bound {r : ℕ}
    (g : NQubitPauliGroupElement (numQubits r))
    (hg : IsNontrivialLogicalOperator g (stabilizerGroup r)) :
    distance r ≤ weight g := by
  refine HomologicalCode.chainWeight_lower_bound_transfers (homologicalCode r) (distance r)
    nontrivial_cycle_weight_lower_bound ?_ g
    ((IsNontrivialLogicalOperator_of_toSubgroup_eq g
      (stabilizerGroup_eq_homological_subgroup r)).mp hg)
  rw [dualCycles_eq_cycles, dualBoundaries_eq_boundaries]
  exact nontrivial_cycle_weight_lower_bound

/-- The X-chain operator of the left side of the patch is a nontrivial logical
operator of weight `2 * r + 1`. -/
theorem exists_logical_weight_eq_distance (r : ℕ) :
    ∃ g, IsNontrivialLogicalOperator g (stabilizerGroup r) ∧ weight g = distance r :=
  ⟨(homologicalCode r).chainXOperator (leftBoundary r),
    (IsNontrivialLogicalOperator_of_toSubgroup_eq _
      (stabilizerGroup_eq_homological_subgroup r)).mpr <|
      (HomologicalCode.chainXOperator_isNontrivialLogical_iff
        (X := homologicalCode r) (leftBoundary r)).mpr
        ⟨leftBoundary_mem_cycles r, leftBoundary_not_mem_boundaries r⟩,
    (HomologicalCode.weight_chainXOperator (X := homologicalCode r) (leftBoundary r)).trans
      (leftBoundary_weight r)⟩

/-- The triangular color code of parameter `r` has distance `2 * r + 1`. -/
theorem has_code_distance (r : ℕ) :
    HasCodeDistance (stabilizerCode r) (distance r) :=
  ⟨Nat.le_add_left 1 _, fun g hg _ => logical_weight_lower_bound g hg,
    exists_logical_weight_eq_distance r⟩

/-- The triangular color code of parameter `r` with its parameters
`[[3r(r+1) + 1, 1, 2r + 1]]`. -/
noncomputable def stabilizerCodeWithDistance (r : ℕ) :
    StabilizerCodeWithDistance (numQubits r) 1 (distance r) where
  toStabilizerCode := stabilizerCode r
  hasDistance := has_code_distance r

/-- The triangular color code of odd distance `d`, with parameters
`[[(3d² + 1)/4, 1, d]]`: the code of parameter `r = d / 2`. -/
noncomputable def codeOfOddDistance (d : ℕ) (hodd : Odd d) :
    StabilizerCodeWithDistance ((3 * d ^ 2 + 1) / 4) 1 d := by
  have hd : distance (d / 2) = d := by
    obtain ⟨r, rfl⟩ := hodd
    unfold distance
    omega
  have hn : numQubits (d / 2) = (3 * d ^ 2 + 1) / 4 := by
    rw [numQubits_eq_distance, hd]
  simpa only [hn, hd] using stabilizerCodeWithDistance (d / 2)

end Quantum.StabilizerGroup.ColorCode

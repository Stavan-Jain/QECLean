import QEC.Stabilizer.Codes.Toric.StabilizerCode

/-!
# Distance of the toric code

The toric code on the `L × L` periodic square lattice, `2 ≤ L`, has distance
`L` (`toricCodeN_distance_eq_L`), so it is a `[[2 * L * L, 2, L]]` code
(`toricStabilizerCodeWithDistance`).

Every nontrivial logical operator has weight at least `L`
(`le_weight_of_isNontrivialLogicalOperator`): its X-part is a cycle and its
Z-part a dual cycle, one of them is not a (dual) boundary, and such chains have
weight at least `L` by `le_edgeWeight_of_not_mem_toricBoundaries` and
`le_edgeWeight_of_not_mem_toricDualBoundaries`. The horizontal X-loop
`horizontalLoopXOperator L` attains the bound.
-/

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement Stabilizer.Homological Stabilizer.Lattice

variable (L : ℕ) [Fact (2 ≤ L)]

/-- Every nontrivial logical operator of the toric code has weight at least
`L`. -/
theorem le_weight_of_isNontrivialLogicalOperator {g : NQubitPauliGroupElement (numQubits L)}
    (hg : IsNontrivialLogicalOperator g (stabilizerGroup L)) : L ≤ weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers (toricHomologicalCode L) L
    (fun _ => le_edgeWeight_of_not_mem_toricBoundaries)
    (fun _ hc hb => le_edgeWeight_of_not_mem_toricDualBoundaries
      (toricHomologicalCode_dualCycles_eq L ▸ hc)
      (toricHomologicalCode_dualBoundaries_eq L ▸ hb))
    g ((IsNontrivialLogicalOperator_of_toSubgroup_eq g
      (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)).1 hg)

/-- The toric code on the `L × L` periodic square lattice has distance `L`. -/
theorem toricCodeN_distance_eq_L : HasCodeDistance (toricStabilizerCode L) L :=
  hasCodeDistance_of_isLeast _ (toricStabilizerCode_subgroup_eq L)
    ⟨⟨horizontalLoopXOperator L, horizontalLoopXOperator_isNontrivialLogical L,
        weight_horizontalLoopXOperator L⟩,
      fun _ ⟨_, hg, hw⟩ => (le_weight_of_isNontrivialLogicalOperator L hg).trans_eq hw⟩

/-- The toric code on the `L × L` periodic square lattice as a
`[[2 * L * L, 2, L]]` stabilizer code with distance. -/
noncomputable def toricStabilizerCodeWithDistance :
    StabilizerCodeWithDistance (2 * L * L) 2 L where
  toStabilizerCode := toricStabilizerCode L
  hasDistance := toricCodeN_distance_eq_L L

end ToricCodeN
end StabilizerGroup
end Quantum

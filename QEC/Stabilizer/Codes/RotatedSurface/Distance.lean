import QEC.Stabilizer.Codes.RotatedSurface.DistanceZ

/-!
# Distance of the rotated surface code

The rotated surface code of odd size `L ≥ 3` has distance `L`
(`rotatedSurfaceCodeN_distance_eq_L`), so it is an `[[L * L, 1, L]]` code
(`rotatedSurfaceStabilizerCodeWithDistance`).

Every nontrivial logical operator has weight at least `L`
(`le_weight_of_isNontrivialLogicalOperator`): its X-part is a cycle and its
Z-part a dual cycle, one of them is not a (dual) boundary, and such chains have
weight at least `L` by `chainWeight_ge_L_of_nontrivial` and
`dual_chainWeight_ge_L_of_nontrivial`. The logical X operator `logicalX L`
attains the bound.
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open NQubitPauliGroupElement Stabilizer.Homological Stabilizer.Lattice.RotatedSurface

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-- Every nontrivial logical operator of the rotated surface code has weight
at least `L`. -/
theorem le_weight_of_isNontrivialLogicalOperator {g : NQubitPauliGroupElement (numQubits L)}
    (hg : IsNontrivialLogicalOperator g
      (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup) :
    L ≤ weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers _ L
    (fun _ => chainWeight_ge_L_of_nontrivial L)
    (fun _ => dual_chainWeight_ge_L_of_nontrivial L) g hg

/-- The rotated surface code on the `L × L` grid has distance `L`. -/
theorem rotatedSurfaceCodeN_distance_eq_L :
    HasCodeDistance (rotatedSurfaceStabilizerCode L) L :=
  hasCodeDistance_of_isLeast _
    (rotatedSurfaceStabilizerCode_toSubgroup_eq_homologicalStabilizerGroup L)
    ⟨⟨logicalX L, logicalX_isNontrivialLogicalOperator L, logicalX_weight_eq_L L⟩,
      fun _ ⟨_, hg, hw⟩ => (le_weight_of_isNontrivialLogicalOperator L hg).trans_eq hw⟩

/-- The rotated surface code on the `L × L` grid as an `[[L * L, 1, L]]`
stabilizer code with distance. -/
noncomputable def rotatedSurfaceStabilizerCodeWithDistance :
    StabilizerCodeWithDistance (numQubits L) 1 L where
  toStabilizerCode := rotatedSurfaceStabilizerCode L
  hasDistance := rotatedSurfaceCodeN_distance_eq_L L

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum

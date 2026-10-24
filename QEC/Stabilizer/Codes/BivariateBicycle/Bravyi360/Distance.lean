import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.OrbitCensus
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomComplete
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopComplete
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DiagonalComplete
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.NonzeroAssembly

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360

/-- Every nontrivial primal logical chain has weight at least twenty-four. -/
theorem distance_lower_bound : ∀ v : Group × Fin 2 → ZMod 2,
    v ∈ complex.cycles → v ∉ complex.boundaries → 24 ≤ complex.chainWeight v := by
  apply distance_floor_of_certificates middle_logical_floor diagonal_boundary
  exact nonzero_shadow_boundary_of_bank reachable_light_normalize_weight
    bottom_complete topBank_boundary

/-- The canonical 360-qubit stabilizer code has distance exactly twenty-four. -/
theorem stabilizerCode_hasDistance24 :
    Quantum.StabilizerGroup.HasCodeDistance stabilizerCode 24 :=
  hasDistance24 distance_lower_bound

/-- The bivariate-bicycle code, with all three parameters certified in its type. -/
noncomputable def stabilizerCodeWithDistance :
    Quantum.StabilizerGroup.StabilizerCodeWithDistance 360 12 24 where
  toStabilizerCode := stabilizerCode
  hasDistance := stabilizerCode_hasDistance24

#print axioms distance_lower_bound
#print axioms stabilizerCode_hasDistance24
#print axioms stabilizerCodeWithDistance
end Quantum.Stabilizer.Homological.BB.Bravyi360

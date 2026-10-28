import QEC.Stabilizer.Codes.Toric.StabilizerCode
import QEC.Stabilizer.Framework.Homological.ToCode

/-!
# The toric code through `HomologicalCode.toStabilizerCode`

`toricStabilizerCode L` (`Toric/StabilizerCode.lean`) is built by hand: one
face and one vertex check are dropped to get an independent generator list of
length `2L² − 2`, and the closure of the trimmed list is shown to be the full
stabilizer group. The generic `HomologicalCode.toStabilizerCode`
(`Framework/Homological/ToCode.lean`) needs none of that: applied to
`toricHomologicalCode L` it takes the closure of all `2L²` checks and reads
the number of logical qubits off `dim H₁`.

This file checks the two constructions against each other. They have the same
stabilizer subgroup (`toricHomologicalCode_toStabilizerCode_subgroup_eq`),
and since `k` is determined by the subgroup
(`StabilizerCode.k_eq_of_toSubgroup_eq`) this already forces
`dim H₁ (toricHomologicalCode L) = 2`
(`toricHomologicalCode_finrank_H1_eq_two`) — a second route to
`toric_finrank_H1_eq_two` of `H1Dimension.lean`, which computes the same
dimension from the kernels of the cut and boundary maps.
-/

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open Stabilizer.Lattice

/-- The generic construction and the hand-trimmed presentation give the same
stabilizer subgroup: both are the closure of all face and vertex checks. -/
theorem toricHomologicalCode_toStabilizerCode_subgroup_eq (L : ℕ) [Fact (2 ≤ L)] :
    (toricHomologicalCode L).toStabilizerCode.toStabilizerGroup.toSubgroup =
      (toricStabilizerCode L).toStabilizerGroup.toSubgroup :=
  (toricStabilizerCode_toSubgroup_eq_homologicalStabilizerGroup L).symm

/-- `dim H₁ = 2` for the toric chain complex, read off the generic code: it
shares its stabilizer subgroup with the `[[2L², 2]]` code
`toricStabilizerCode L`, and `k` is a function of the subgroup. -/
theorem toricHomologicalCode_finrank_H1_eq_two (L : ℕ) [Fact (2 ≤ L)] :
    Module.finrank (ZMod 2) (toricHomologicalCode L).H1 = 2 :=
  StabilizerCode.k_eq_of_toSubgroup_eq (toricHomologicalCode L).toStabilizerCode
    (toricStabilizerCode L) (toricHomologicalCode_toStabilizerCode_subgroup_eq L)

end ToricCodeN
end StabilizerGroup
end Quantum

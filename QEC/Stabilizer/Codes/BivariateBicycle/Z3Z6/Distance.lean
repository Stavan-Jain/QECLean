/-
# `d([[72,4,8]]) = 8` at the chain and Pauli levels

The assembly of the second doubling instance through the parametric layer
(`BBDoubling.lean`): given the base floor (`BaseDistance.lean`), the
homotopy (R) (`DeckHomotopy.lean`), the dangerous floor (`Dangerous.lean`),
the Smith-coset floor (`SafeFloor.lean`) and the tight witness
(`Witness.lean`),

* `pair72_chain_distance_eq_8` — 8 is the least weight of a nontrivial
  cycle of the cover complex;
* `pair72_pauli_distance_eq_8` — 8 is the least weight of a nontrivial
  logical operator of the cover's homological stabilizer group.

Every input was discharged in the sibling files; both statements are
unconditional (axiom bar: the standard three + `Lean.ofReduceBool` from
the kernel sweeps).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Dangerous
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SafeFloor

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

/-- The safe floor, from (R) and the Smith-coset floor. -/
theorem pair72_safeFloor : coverData.SafeFloor 8 :=
  coverData.safeFloor_of_seamCosetFloor homotopyR pair72_seamCosetFloor

/-- **Chain-level `d(cover) = 2·d(base) = 8`.** -/
theorem pair72_chain_distance_eq_8 :
    IsLeast {w : ℕ | ∃ v : G72 × Fin 2 → ZMod 2,
      v ∈ coverData.coverComplex.cycles ∧
      v ∉ coverData.coverComplex.boundaries ∧
      coverData.coverComplex.chainWeight v = w} 8 := by
  have h := coverData.chain_distance_eq_double (d := 4)
    base36_strong_floor pair72_dangerousFloorNZ pair72_safeFloor
    uStar36 uStar36_mem_cycles chainWeight_uStar36
    tauUStar36_not_mem_boundaries
  norm_num at h
  exact h

/-- **Pauli-level `d(cover) = 8`**: 8 is the least weight of a nontrivial
logical operator of the `[[72,4,8]]` homological stabilizer group. -/
theorem pair72_pauli_distance_eq_8 :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement coverData.coverComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        coverData.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 8 := by
  have h := coverData.pauli_distance_eq_double (d := 4)
    base36_strong_floor pair72_dangerousFloorNZ pair72_safeFloor
    uStar36 uStar36_mem_cycles chainWeight_uStar36
    tauUStar36_not_mem_boundaries
  norm_num at h
  exact h

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

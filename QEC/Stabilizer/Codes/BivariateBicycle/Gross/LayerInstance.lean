/-
# Gross distance through the parametric doubling machinery

The cover bundle lives in `CoverTransfer.lean`. Its base floor is an instance
of `BBSmallCycle`, its deck homotopy uses the generic Bézout theorem, its
hexagon and D-pair bounds use the generic logical-floor rungs, and its safe
sector uses the generic seam-coset reduction. This file discharges the
remaining classification and confined-floor inputs, then applies the generic
chain and Pauli assemblies. `Distance.lean` packages this same result.

Gross-specific inputs remain the kernel-checked polynomial, support-shape,
CRT/coset, and tight-witness certificates. All geometric reductions are shared
with other `XDoubleCoverData` instances.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImAssembly
import QEC.Stabilizer.Framework.Homological.BBDoubling

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `fiberSum (Prod.map ⇑coverPi id)` unfold deep
-- `Prod`/`ZMod` instance chains, exactly as in `CoverTransfer.lean`.
set_option maxRecDepth 4096

/-! ## The remaining layer inputs -/

/-- **`DangerousFloorNZ 12`** — (M) on the `b ≠ 0` rungs, unconditional via the
light-stabilizer classification. -/
theorem grossCoverData_dangerousFloorNZ : grossCoverData.DangerousFloorNZ 12 :=
  LightStab.dangerous_sector_unconditional

/-- **`SafeFloor 12`** — (M-im), unconditional via `mimBound_holds`. -/
theorem grossCoverData_safeFloor : grossCoverData.SafeFloor 12 :=
  grossCoverData.safeFloor_of_seamCosetFloor
    grossCoverData_deckTrivial LightStab.mimBound_holds

/-! ## Interface identities (documentation-grade: the layer's sector `Prop`s
are definitionally the `Assembly.lean` ones) -/

/-- The legacy dangerous-sector proposition is the generic floor. -/
theorem grossCoverData_dangerousFloorNZ_iff :
    grossCoverData.DangerousFloorNZ 12 ↔ DangerousSectorGe12 :=
  Iff.rfl

/-- The legacy safe-sector proposition is the generic floor. -/
theorem grossCoverData_safeFloor_iff :
    grossCoverData.SafeFloor 12 ↔ SafeSectorGe12 :=
  Iff.rfl

/-! ## The layer-routed unconditional endpoints -/

/-- **Unconditional chain-level `d(gross) = 12`, through the parametric layer**:
12 is the least weight of a nontrivial cycle of the gross complex.
Statement-identical to `gross_chain_distance_eq_12_of_sectors` with the sector
hypotheses discharged. -/
theorem gross_chain_distance_eq_12 :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 :=
  grossCoverData.chain_distance_eq_double_of_logicalFloor
    grossCoverData_logicalFloor grossCoverData_dangerousFloorNZ
    grossCoverData_safeFloor uStar uStar_mem_cycles chainWeight_uStar
    tauUStar_not_mem_boundaries

/-- **Unconditional Pauli-level `d(gross) = 12`, through the parametric layer**:
12 is the least weight of a nontrivial logical operator of the gross homological
stabilizer group. Statement-identical to `gross_pauli_distance_eq_12_of_sectors`
with the sector hypotheses discharged. -/
theorem gross_pauli_distance_eq_12 :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 :=
  grossCoverData.pauli_distance_eq_double_of_logicalFloor
    grossCoverData_logicalFloor grossCoverData_dangerousFloorNZ
    grossCoverData_safeFloor uStar uStar_mem_cycles chainWeight_uStar
    tauUStar_not_mem_boundaries

end BB
end Homological
end Stabilizer
end Quantum

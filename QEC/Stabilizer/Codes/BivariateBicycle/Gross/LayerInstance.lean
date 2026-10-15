/-
# Gross distance through the parametric doubling machinery

The cover bundle lives in `CoverTransfer.lean`. Its base floor is an instance
of `BBSmallCycle`, its deck homotopy uses the generic Bézout theorem, its
light base boundaries are admissible for the generic logical-floor rungs
(hexagons and D-pairs), and its seam-coset floor comes from the
Brouwer–Zimmermann certificate. This file reads the light-boundary census as
admissibility and proves the unconditional distances as single applications of
the packaged Doubling theorem (`chain_distance_eq_double_of_admissible`,
`pauli_distance_eq_double_of_admissible`). `Distance.lean` packages the
Pauli-level result. The two sector floors are also kept as standalone
theorems (`grossCoverData_dangerousFloorNZ`, `grossCoverData_safeFloor`).

Gross-specific inputs remain the kernel-checked polynomial, support-shape,
Brouwer–Zimmermann (`SeamBZ`), and tight-witness certificates. All geometric
reductions are shared with other `XDoubleCoverData` instances.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SeamBZ
import QEC.Stabilizer.Framework.Homological.BBDoubling

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `fiberSum (Prod.map ⇑coverPi id)` unfold deep
-- `Prod`/`ZMod` instance chains, exactly as in `CoverTransfer.lean`.
set_option maxRecDepth 4096

/-! ## The two sector floors, standalone

The endpoints below do not use these: the packaged Doubling theorem derives
both floors from its inputs. They are kept for users of the sector-floor
interface. -/

/-- **`DangerousFloorNZ 12`** — (M) on the `b ≠ 0` rungs, unconditional via the
light-boundary census of the Brouwer–Zimmermann certificate. -/
theorem grossCoverData_dangerousFloorNZ : grossCoverData.DangerousFloorNZ 12 :=
  GrossBZ.dangerousSector_bz

/-- **`SafeFloor 12`** — (M-im), unconditional via the Brouwer–Zimmermann
seam-coset floor. -/
theorem grossCoverData_safeFloor : grossCoverData.SafeFloor 12 :=
  grossCoverData.safeFloor_of_seamCosetFloor
    grossCoverData_deckTrivial GrossBZ.mimBound_bz

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

/-! ## (H5): the light-boundary census as admissibility -/

/-- **(H5) for Gross**: every nonzero bb72 boundary of weight `< 12` is
admissible — the light-boundary census
`GrossBZ.lightStabilizerClassification_bz` (hexagons and D-pairs). -/
theorem grossCoverData_lightBoundaryAdmissible :
    ∀ b : BaseGroup × Fin 2 → ZMod 2, b ∈ grossCoverData.baseComplex.boundaries →
      b ≠ 0 → grossCoverData.baseComplex.chainWeight b < 2 * 6 →
      grossCoverData.LightBoundaryAdmissible 6 b :=
  lightBoundaryAdmissible_of_classification
    GrossBZ.lightStabilizerClassification_bz

/-! ## The unconditional endpoints, by the packaged Doubling theorem

Each endpoint is one application of the generic Doubling theorem, whose five
inputs are: (H1) `grossCoverData_logicalFloor`, (H2) the witness `uStar`,
(H3) `grossCoverData_deckTrivial`, (H4) `GrossBZ.mimBound_bz`, and (H5)
`grossCoverData_lightBoundaryAdmissible`. -/

/-- **Unconditional chain-level `d(gross) = 12`, by the Doubling theorem**:
12 is the least weight of a nontrivial cycle of the gross complex.
Statement-identical to `gross_chain_distance_eq_12_of_sectors` with the sector
hypotheses discharged; proved as one application of
`chain_distance_eq_double_of_admissible`. -/
theorem gross_chain_distance_eq_12 :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 :=
  grossCoverData.chain_distance_eq_double_of_admissible
    grossCoverData_logicalFloor uStar uStar_mem_cycles chainWeight_uStar
    tauUStar_not_mem_boundaries grossCoverData_deckTrivial GrossBZ.mimBound_bz
    grossCoverData_lightBoundaryAdmissible

/-- **Unconditional Pauli-level `d(gross) = 12`, by the Doubling theorem**:
12 is the least weight of a nontrivial logical operator of the gross homological
stabilizer group. Statement-identical to `gross_pauli_distance_eq_12_of_sectors`
with the sector hypotheses discharged; proved as one application of
`pauli_distance_eq_double_of_admissible`. -/
theorem gross_pauli_distance_eq_12 :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 :=
  grossCoverData.pauli_distance_eq_double_of_admissible
    grossCoverData_logicalFloor uStar uStar_mem_cycles chainWeight_uStar
    tauUStar_not_mem_boundaries grossCoverData_deckTrivial GrossBZ.mimBound_bz
    grossCoverData_lightBoundaryAdmissible

end BB
end Homological
end Stabilizer
end Quantum

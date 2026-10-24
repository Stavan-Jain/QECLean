import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BaseSparse
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BaseCycleCensus

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
open F2Mask.Trellis.Bravyi90
set_option maxRecDepth 10000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The small-cycle syndrome columns are bounded by the number of base checks. -/
theorem baseCensusSyndrome_bounded : ∀ p ∈ cycleSyndrome, p.2 < 2 ^ 45 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The census uses the actual three-check syndrome of each base qubit. -/
theorem baseCensusSyndrome_columns : ∀ q : BaseGroup × Fin 2,
    reconX cycleSyndrome (2 ^ (baseQubitEnum q).val) = baseSyndromeMask q := by
  decide +kernel


set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every stored elementary base boundary is a sparse physical face check. -/
theorem baseBoundaryWindow_columns : ∀ p ∈ baseBoundaryWindow,
    ∃ i : Fin 45, p.2 = baseFaceMask (baseFaceEnum.symm i) := by
  decide +kernel


end Quantum.Stabilizer.Homological.BB.Bravyi360

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.ReachabilityData
import QEC.Stabilizer.Framework.Homological.Certificate.MaskFiber
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Sparse

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask ReachabilityData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The43-dimensional candidate space in bottom certificate coordinates. -/
noncomputable def reachableMap : (Fin 43 → ZMod 2) →ₗ[ZMod 2] (BaseGroup × Fin 2 → ZMod 2) :=
  reconLinear (Equiv.refl (Fin 43)) baseQubitEnum reachableGenerators
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinates of a bottom chain in the candidate space. -/
noncomputable def reachableDecode : (BaseGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 43 → ZMod 2) :=
  reconLinear baseQubitEnum (Equiv.refl (Fin 43)) reachableDecoder
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The residual of the43-dimensional projection factors through the top syndrome. -/
noncomputable def reachableResidual : (Group → ZMod 2) →ₗ[ZMod 2] (BaseGroup × Fin 2 → ZMod 2) :=
  reconLinear faceEnum baseQubitEnum reachableCorrection

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Direct sheet formula for the two-level shadow, used in sparse certificates. -/
noncomputable def bottomShadowSheets (v : Group × Fin 2 → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  baseCover.sheet0 (topCover.sheet0 v + topCover.sheet1 v) +
    baseCover.sheet1 (topCover.sheet0 v + topCover.sheet1 v)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The sparse sheet formula is the composed pushforward. -/
theorem bottomShadow_eq_sheets (v : Group × Fin 2 → ZMod 2) :
    baseCover.push1 (topCover.push1 v) = bottomShadowSheets v := by
  rw [← topCover.sheets_add_eq_push, ← baseCover.sheets_add_eq_push]
  rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The direct image equation is checked using three syndrome bits per qubit. -/
theorem reachable_columns : ∀ q : Group × Fin 2,
    (reconX reachableGenerators
      (reconX reachableDecoder
        (2 ^ (baseQubitEnum (baseProjection (topProjection q.1), q.2)).val))) ^^^
      reconX reachableCorrection (syndromeMask q) =
        2 ^ (baseQubitEnum (baseProjection (topProjection q.1), q.2)).val := by
  decide +kernel

end Quantum.Stabilizer.Homological.BB.Bravyi360

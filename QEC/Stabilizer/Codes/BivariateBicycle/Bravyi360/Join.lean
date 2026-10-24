import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Defs
import QEC.Stabilizer.Framework.Homological.Certificate.MaskJoin

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse columns embedding the lower x sheet in the middle code. -/
noncomputable def bottomLeft : List (Nat × Nat) :=
  (List.range 90).map fun i => (i, 2 ^ ((i / 45) * 90 + i % 45))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse columns embedding the upper x sheet in the middle code. -/
noncomputable def bottomRight : List (Nat × Nat) :=
  (List.range 90).map fun i => (i, 2 ^ ((i / 45) * 90 + i % 45 + 45))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse columns embedding the lower y sheet in the top code. -/
noncomputable def topLeft : List (Nat × Nat) :=
  (List.range 180).map fun i => (i, 2 ^ ((i / 90) * 180 + (i % 90 / 3) * 6 + i % 3))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse columns embedding the upper y sheet in the top code. -/
noncomputable def topRight : List (Nat × Nat) :=
  (List.range 180).map fun i => (i, 2 ^ ((i / 90) * 180 + (i % 90 / 3) * 6 + i % 3 + 3))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The bottom sheet embeddings fit within 180 bits. -/
theorem bottomJoin_bounded :
    (∀ p ∈ bottomLeft, p.2 < 2 ^ 180) ∧ (∀ p ∈ bottomRight, p.2 < 2 ^ 180) := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The top sheet embeddings fit within 360 bits. -/
theorem topJoin_bounded :
    (∀ p ∈ topLeft, p.2 < 2 ^ 360) ∧ (∀ p ∈ topRight, p.2 < 2 ^ 360) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Joining a first sheet and its bottom shadow gives the middle mask. -/
noncomputable def bottomJoin (a beta : Nat) : Nat :=
  reconX bottomLeft a ^^^ reconX bottomRight (a ^^^ beta)
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Joining a first sheet and its middle shadow gives the top mask. -/
noncomputable def topJoin (a beta : Nat) : Nat :=
  reconX topLeft a ^^^ reconX topRight (a ^^^ beta)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The bottom sheet embeddings reconstruct each point-mass qubit. -/
theorem bottomJoin_columns : ∀ q : MiddleGroup × Fin 2,
    bottomJoin (if baseSection (baseProjection q.1) = q.1 then
      2 ^ (baseQubitEnum (baseProjection q.1, q.2)).val else 0)
      (2 ^ (baseQubitEnum (baseProjection q.1, q.2)).val) =
        2 ^ (middleQubitEnum q).val := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The top sheet embeddings reconstruct each point-mass qubit. -/
theorem topJoin_columns : ∀ q : Group × Fin 2,
    topJoin (if topSection (topProjection q.1) = q.1 then
      2 ^ (middleQubitEnum (topProjection q.1, q.2)).val else 0)
      (2 ^ (middleQubitEnum (topProjection q.1, q.2)).val) =
        2 ^ (qubitEnum q).val := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The bottom join is the actual mask of a middle chain. -/
theorem maskOf_middle_eq_join (v : MiddleGroup × Fin 2 → ZMod 2) :
    maskOf middleQubitEnum v = bottomJoin (maskOf baseQubitEnum (baseCover.sheet0 v))
      (maskOf baseQubitEnum (baseCover.push1 v)) := by
  apply baseCover.maskOf_eq_join_of_basis baseQubitEnum middleQubitEnum
    bottomLeft bottomRight bottomJoin_bounded.1 bottomJoin_bounded.2
  intro q
  rw [baseCover.sheet1_eq_sheet0_add_push, maskOf_add,
    baseCover.maskOf_sheet0_single, baseCover.push1_single, maskOf_single]
  exact bottomJoin_columns q

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The top join is the actual mask of a top chain. -/
theorem maskOf_top_eq_join (v : Group × Fin 2 → ZMod 2) :
    maskOf qubitEnum v = topJoin (maskOf middleQubitEnum (topCover.sheet0 v))
      (maskOf middleQubitEnum (topCover.push1 v)) := by
  apply topCover.maskOf_eq_join_of_basis middleQubitEnum qubitEnum
    topLeft topRight topJoin_bounded.1 topJoin_bounded.2
  intro q
  rw [topCover.sheet1_eq_sheet0_add_push, maskOf_add,
    topCover.maskOf_sheet0_single, topCover.push1_single, maskOf_single]
  exact topJoin_columns q

end Quantum.Stabilizer.Homological.BB.Bravyi360

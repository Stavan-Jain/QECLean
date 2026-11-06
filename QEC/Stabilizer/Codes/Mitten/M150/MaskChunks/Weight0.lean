/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.SweepAdapters
import QEC.Stabilizer.Codes.Mitten.M150.MaskEnumeration

namespace Quantum.Stabilizer.Homological.LP.M150
open F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def masks0S512Leaf0 : List Nat := [
  0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks0S512Leaf0_enumerates. -/
theorem masks0S512Leaf0_enumerates : masks0S512Leaf0 = (masksOfWt 30 0).map (fun m => m ||| 0) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def masks0S512Chunk0 : List Nat := masks0S512Leaf0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def masks0S512Chunks : List (List Nat) := [
  masks0S512Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def masks0S512Cover : MaskCover 30 0 0 := MaskCover.leaf masks0S512Leaf0
  masks0S512Leaf0_enumerates

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks0S512_cover. -/
theorem masks0S512_cover : masks0S512Chunks.flatten = masksOfWt 30 0 := by
  exact MaskCover.cover_zero masks0S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks0S512Chunk0_bound. -/
theorem masks0S512Chunk0_bound : ∀ x ∈ masks0S512Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 0 x
  rw [← masks0S512_cover]
  exact List.mem_flatten.mpr ⟨masks0S512Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def masks0S2048Chunk0 : List Nat := masks0S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def masks0S2048Chunks : List (List Nat) := [
  masks0S2048Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def masks0S2048Cover : MaskCover 30 0 0 := masks0S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks0S2048_cover. -/
theorem masks0S2048_cover : masks0S2048Chunks.flatten = masksOfWt 30 0 := by
  exact MaskCover.cover_zero masks0S2048Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks0S2048Chunk0_bound. -/
theorem masks0S2048Chunk0_bound : ∀ x ∈ masks0S2048Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 0 x
  rw [← masks0S2048_cover]
  exact List.mem_flatten.mpr ⟨masks0S2048Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def outerMasks0S256Chunk0 : List Nat := masks0S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def outerMasks0S256Chunks : List (List Nat) := [
  outerMasks0S256Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def outerMasks0S256Cover : MaskCover 30 0 0 := masks0S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks0S256_cover. -/
theorem outerMasks0S256_cover : outerMasks0S256Chunks.flatten = masksOfWt 30 0 := by
  exact MaskCover.cover_zero outerMasks0S256Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks0S256Chunk0_bound. -/
theorem outerMasks0S256Chunk0_bound : ∀ x ∈ outerMasks0S256Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 0 x
  rw [← outerMasks0S256_cover]
  exact List.mem_flatten.mpr ⟨outerMasks0S256Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def outerMasks0S2048Chunk0 : List Nat := masks0S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def outerMasks0S2048Chunks : List (List Nat) := [
  outerMasks0S2048Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def outerMasks0S2048Cover : MaskCover 30 0 0 := masks0S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks0S2048_cover. -/
theorem outerMasks0S2048_cover : outerMasks0S2048Chunks.flatten = masksOfWt 30 0 := by
  exact MaskCover.cover_zero outerMasks0S2048Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks0S2048Chunk0_bound. -/
theorem outerMasks0S2048Chunk0_bound : ∀ x ∈ outerMasks0S2048Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 0 x
  rw [← outerMasks0S2048_cover]
  exact List.mem_flatten.mpr ⟨outerMasks0S2048Chunk0,
    List.mem_cons_self, hx⟩

end Quantum.Stabilizer.Homological.LP.M150

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
def masks1S512Leaf0 : List Nat := [
  1, 2, 4, 8, 16, 32,
  64, 128, 256, 512, 1024, 2048,
  4096, 8192, 16384, 32768, 65536, 131072,
  262144, 524288, 1048576, 2097152, 4194304, 8388608,
  16777216, 33554432, 67108864, 134217728, 268435456, 536870912
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks1S512Leaf0_enumerates. -/
theorem masks1S512Leaf0_enumerates : masks1S512Leaf0 = (masksOfWt 30 1).map (fun m => m ||| 0) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def masks1S512Chunk0 : List Nat := masks1S512Leaf0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def masks1S512Chunks : List (List Nat) := [
  masks1S512Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def masks1S512Cover : MaskCover 30 1 0 := MaskCover.leaf masks1S512Leaf0
  masks1S512Leaf0_enumerates

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks1S512_cover. -/
theorem masks1S512_cover : masks1S512Chunks.flatten = masksOfWt 30 1 := by
  exact MaskCover.cover_zero masks1S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks1S512Chunk0_bound. -/
theorem masks1S512Chunk0_bound : ∀ x ∈ masks1S512Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 1 x
  rw [← masks1S512_cover]
  exact List.mem_flatten.mpr ⟨masks1S512Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def masks1S2048Chunk0 : List Nat := masks1S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def masks1S2048Chunks : List (List Nat) := [
  masks1S2048Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def masks1S2048Cover : MaskCover 30 1 0 := masks1S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks1S2048_cover. -/
theorem masks1S2048_cover : masks1S2048Chunks.flatten = masksOfWt 30 1 := by
  exact MaskCover.cover_zero masks1S2048Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks1S2048Chunk0_bound. -/
theorem masks1S2048Chunk0_bound : ∀ x ∈ masks1S2048Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 1 x
  rw [← masks1S2048_cover]
  exact List.mem_flatten.mpr ⟨masks1S2048Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def outerMasks1S256Chunk0 : List Nat := masks1S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def outerMasks1S256Chunks : List (List Nat) := [
  outerMasks1S256Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def outerMasks1S256Cover : MaskCover 30 1 0 := masks1S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks1S256_cover. -/
theorem outerMasks1S256_cover : outerMasks1S256Chunks.flatten = masksOfWt 30 1 := by
  exact MaskCover.cover_zero outerMasks1S256Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks1S256Chunk0_bound. -/
theorem outerMasks1S256Chunk0_bound : ∀ x ∈ outerMasks1S256Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 1 x
  rw [← outerMasks1S256_cover]
  exact List.mem_flatten.mpr ⟨outerMasks1S256Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def outerMasks1S2048Chunk0 : List Nat := masks1S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def outerMasks1S2048Chunks : List (List Nat) := [
  outerMasks1S2048Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def outerMasks1S2048Cover : MaskCover 30 1 0 := masks1S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks1S2048_cover. -/
theorem outerMasks1S2048_cover : outerMasks1S2048Chunks.flatten = masksOfWt 30 1 := by
  exact MaskCover.cover_zero outerMasks1S2048Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks1S2048Chunk0_bound. -/
theorem outerMasks1S2048Chunk0_bound : ∀ x ∈ outerMasks1S2048Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 1 x
  rw [← outerMasks1S2048_cover]
  exact List.mem_flatten.mpr ⟨outerMasks1S2048Chunk0,
    List.mem_cons_self, hx⟩

end Quantum.Stabilizer.Homological.LP.M150

/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.MaskChunks
import QEC.Stabilizer.Codes.Mitten.M150.SweepMaps
import QEC.Stabilizer.Codes.Mitten.M150.PackedGridSweep
import QEC.Stabilizer.Codes.Mitten.M150.CensusTables

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y0Certs : List (Nat × Nat) := [
  (152, 188), (170, 192), (1623, 466), (1694, 471)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y0_check. -/
theorem Z0Split80A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y0_pairs. -/
theorem Z0Split80A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk0_bound y hy)
  · exact Z0Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y1Certs : List (Nat × Nat) := [
  (334, 523), (417, 528)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y1_check. -/
theorem Z0Split80A0X0Y1_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y1_pairs. -/
theorem Z0Split80A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk1_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk1_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk1_bound y hy)
  · exact Z0Split80A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y2Certs : List (Nat × Nat) := [
  (6, 637), (735, 715)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y2_check. -/
theorem Z0Split80A0X0Y2_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y2_pairs. -/
theorem Z0Split80A0X0Y2_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y2Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk2_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk2
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk2_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk2_bound y hy)
  · exact Z0Split80A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y3Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y3_check. -/
theorem Z0Split80A0X0Y3_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y3_pairs. -/
theorem Z0Split80A0X0Y3_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y3Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk3_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk3
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk3_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk3_bound y hy)
  · exact Z0Split80A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y4Certs : List (Nat × Nat) := [
  (220, 948), (619, 983), (927, 1000), (1087, 1008)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y4_check. -/
theorem Z0Split80A0X0Y4_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y4_pairs. -/
theorem Z0Split80A0X0Y4_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y4Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk4_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk4
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk4_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk4_bound y hy)
  · exact Z0Split80A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y5Certs : List (Nat × Nat) := [
  (717, 1097), (1096, 1112), (1274, 1117), (1471, 1127)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y5_check. -/
theorem Z0Split80A0X0Y5_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y5_pairs. -/
theorem Z0Split80A0X0Y5_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y5Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk5_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk5
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk5_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk5_bound y hy)
  · exact Z0Split80A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y6Certs : List (Nat × Nat) := [
  (520, 1202), (681, 1220), (1284, 1260)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y6_check. -/
theorem Z0Split80A0X0Y6_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y6_pairs. -/
theorem Z0Split80A0X0Y6_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y6Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk6_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk6
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk6_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk6_bound y hy)
  · exact Z0Split80A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y7Certs : List (Nat × Nat) := [
  (8, 1306), (146, 1334), (1502, 1419)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y7_check. -/
theorem Z0Split80A0X0Y7_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y7_pairs. -/
theorem Z0Split80A0X0Y7_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y7Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk7_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk7
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk7_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk7_bound y hy)
  · exact Z0Split80A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y8Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y8_check. -/
theorem Z0Split80A0X0Y8_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y8_pairs. -/
theorem Z0Split80A0X0Y8_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk8,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y8Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk8_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk8_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk8
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk8_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk8_bound y hy)
  · exact Z0Split80A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y9Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y9_check. -/
theorem Z0Split80A0X0Y9_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y9_pairs. -/
theorem Z0Split80A0X0Y9_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk9,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y9Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk9_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk9_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk9
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk9_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk9_bound y hy)
  · exact Z0Split80A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y10Certs : List (Nat × Nat) := [
  (676, 1637), (982, 1654), (1817, 1698), (1880, 1703)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y10_check. -/
theorem Z0Split80A0X0Y10_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y10_pairs. -/
theorem Z0Split80A0X0Y10_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk10,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y10Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk10_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk10_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk10
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk10_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk10_bound y hy)
  · exact Z0Split80A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y11Certs : List (Nat × Nat) := [
  (244, 1716), (527, 1725)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y11_check. -/
theorem Z0Split80A0X0Y11_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y11Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y11_pairs. -/
theorem Z0Split80A0X0Y11_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk11,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y11Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk11_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk11_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk11
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk11_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk11_bound y hy)
  · exact Z0Split80A0X0Y11_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y12Certs : List (Nat × Nat) := [
  (574, 1799), (1371, 1856), (1482, 1864), (1788, 1884)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y12_check. -/
theorem Z0Split80A0X0Y12_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y12Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y12_pairs. -/
theorem Z0Split80A0X0Y12_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk12,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y12Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk12_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk12_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk12
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk12_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk12_bound y hy)
  · exact Z0Split80A0X0Y12_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y13Certs : List (Nat × Nat) := [
  (543, 1909), (635, 1916)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y13_check. -/
theorem Z0Split80A0X0Y13_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y13Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y13_pairs. -/
theorem Z0Split80A0X0Y13_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk13,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y13Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk13_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk13_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk13
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk13_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk13_bound y hy)
  · exact Z0Split80A0X0Y13_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y14Certs : List (Nat × Nat) := [
  (153, 1965), (782, 2006)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y14_check. -/
theorem Z0Split80A0X0Y14_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y14Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y14_pairs. -/
theorem Z0Split80A0X0Y14_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk14,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y14Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk14_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk14_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk14
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk14_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk14_bound y hy)
  · exact Z0Split80A0X0Y14_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y15Certs : List (Nat × Nat) := [
  (881, 2069)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y15_check. -/
theorem Z0Split80A0X0Y15_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y15Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y15_pairs. -/
theorem Z0Split80A0X0Y15_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk15,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y15Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk15_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk15_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk15
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk15_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk15_bound y hy)
  · exact Z0Split80A0X0Y15_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y16Certs : List (Nat × Nat) := [
  (501, 2164), (721, 2175), (893, 2187), (1594, 2227), (2003, 2251)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y16_check. -/
theorem Z0Split80A0X0Y16_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y16Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y16_pairs. -/
theorem Z0Split80A0X0Y16_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk16,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y16Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk16_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk16_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk16
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk16_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk16_bound y hy)
  · exact Z0Split80A0X0Y16_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y17Certs : List (Nat × Nat) := [
  (339, 2267), (973, 2305), (1623, 2322)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y17_check. -/
theorem Z0Split80A0X0Y17_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y17Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y17_pairs. -/
theorem Z0Split80A0X0Y17_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk17,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y17Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk17_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S2048Chunk17_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S2048Chunk17
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk17_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks4S2048Chunk17_bound y hy)
  · exact Z0Split80A0X0Y17_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0_pairs. -/
theorem Z0Split80A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split80A0X0Y0_pairs x hx y hy hw
  · exact Z0Split80A0X0Y1_pairs x hx y hy hw
  · exact Z0Split80A0X0Y2_pairs x hx y hy hw
  · exact Z0Split80A0X0Y3_pairs x hx y hy hw
  · exact Z0Split80A0X0Y4_pairs x hx y hy hw
  · exact Z0Split80A0X0Y5_pairs x hx y hy hw
  · exact Z0Split80A0X0Y6_pairs x hx y hy hw
  · exact Z0Split80A0X0Y7_pairs x hx y hy hw
  · exact Z0Split80A0X0Y8_pairs x hx y hy hw
  · exact Z0Split80A0X0Y9_pairs x hx y hy hw
  · exact Z0Split80A0X0Y10_pairs x hx y hy hw
  · exact Z0Split80A0X0Y11_pairs x hx y hy hw
  · exact Z0Split80A0X0Y12_pairs x hx y hy hw
  · exact Z0Split80A0X0Y13_pairs x hx y hy hw
  · exact Z0Split80A0X0Y14_pairs x hx y hy hw
  · exact Z0Split80A0X0Y15_pairs x hx y hy hw
  · exact Z0Split80A0X0Y16_pairs x hx y hy hw
  · exact Z0Split80A0X0Y17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0_pairs. -/
theorem Z0Split80A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split80A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split80_check. -/
theorem Z0Split80_check : checkSplit m4TZ0 (4, 0, 4, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split80A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split81A0X0Y0Certs : List (Nat × Nat) := [
  (45, 130), (870, 657), (4381, 355), (4713, 531), (6967, 671),
  (8400, 341), (9221, 816), (10306, 247), (13239, 804), (13896, 1121),
  (15143, 749), (16777, 501), (16791, 509), (19258, 783), (21000, 592),
  (26377, 152), (26853, 470), (29963, 1071), (29988, 1084), (30651, 329),
  (31531, 854), (34332, 1250), (36076, 1089), (36666, 282), (38863, 394),
  (38929, 442), (39971, 1007), (43476, 746), (43500, 761), (49834, 876),
  (49979, 952), (51580, 751), (55436, 603), (56796, 210), (60684, 1266)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0Y0_check. -/
theorem Z0Split81A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0Y0_pairs. -/
theorem Z0Split81A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split81A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split81A0X0Y1Certs : List (Nat × Nat) := [
  (2059, 1319), (2126, 1356), (3491, 2021), (6393, 1458), (6613, 1526),
  (8599, 1515), (15547, 1959), (15781, 2040), (18345, 1317), (19866, 2046),
  (23376, 1780), (23778, 1995), (24675, 1430), (25024, 1582), (26506, 1324),
  (30706, 1389), (36417, 2196), (37380, 1645), (41482, 1660), (41519, 1680),
  (43130, 1491), (45981, 1897), (46892, 1342), (47649, 1688), (49055, 1404),
  (51115, 1414), (54722, 2182), (55743, 1668), (57057, 1332), (59370, 1475)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0Y1_check. -/
theorem Z0Split81A0X0Y1_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split81A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0Y1_pairs. -/
theorem Z0Split81A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split81A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split81A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0_pairs. -/
theorem Z0Split81A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split81A0X0Y0_pairs x hx y hy hw
  · exact Z0Split81A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0_pairs. -/
theorem Z0Split81A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split81A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split81_check. -/
theorem Z0Split81_check : checkSplit m4TZ0 (4, 1, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split81A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split82A0X0Y0Certs : List (Nat × Nat) := [
  (2223, 208), (4133, 930), (4487, 545), (4502, 606), (4877, 383),
  (9057, 1751), (10843, 2050), (11872, 498), (13232, 777), (13922, 38),
  (18122, 1335), (18797, 384), (19379, 1040), (19535, 2000), (20702, 1151),
  (20720, 1274), (20906, 126), (21509, 844), (25126, 1581), (25945, 1302),
  (26162, 245), (33478, 2137), (34408, 189), (34483, 467), (37361, 1955),
  (39394, 1066), (39873, 1344), (42488, 1376), (43519, 103), (46989, 68),
  (47257, 1298), (49530, 1893), (50164, 547), (50465, 50), (51524, 845),
  (52026, 1158), (52104, 1609), (55170, 1764), (55187, 1913), (55333, 352),
  (56424, 1466), (59373, 918), (60023, 2222), (61841, 281), (63114, 179),
  (63659, 589), (64262, 1499), (70212, 752), (71631, 1360), (73679, 658),
  (76243, 468), (76354, 1002), (79177, 66), (79434, 1172), (80139, 392),
  (82559, 1648), (83147, 246), (83676, 635), (87686, 1113), (87785, 1717),
  (88126, 1149), (89250, 289), (94404, 69), (94438, 190), (96502, 1795),
  (97849, 2099), (98570, 1154), (98772, 131), (99924, 1467), (100245, 848),
  (100415, 1783), (100621, 541), (101284, 1777), (106116, 2103), (106126, 2160),
  (106327, 800), (107403, 1983)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X0Y0_check. -/
theorem Z0Split82A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X0Y0_pairs. -/
theorem Z0Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split82A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X0_pairs. -/
theorem Z0Split82A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split82A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split82A0X1Y0Certs : List (Nat × Nat) := [
  (525, 363), (892, 122), (1419, 451), (1734, 2239), (2076, 1600),
  (5383, 654), (6637, 444), (7232, 1247), (7796, 2033), (10286, 1308),
  (10833, 1984), (11630, 1519), (12508, 1573), (14149, 1003), (14197, 1299),
  (17440, 184), (17768, 1808), (18474, 874), (21190, 1469), (21306, 2201),
  (22334, 590), (23076, 120), (28190, 1718), (28223, 1947), (28633, 1759),
  (29748, 683), (32445, 1144), (33485, 2192), (39215, 254), (39371, 941),
  (39883, 1424), (40673, 931), (44559, 813), (45322, 332), (45900, 975),
  (46037, 1769), (46163, 220), (46244, 525), (46686, 554), (50580, 484),
  (51988, 959), (52575, 1894), (52994, 1762), (54794, 2149), (55020, 914),
  (56426, 1480), (56509, 1988), (58562, 1248), (59675, 325), (64433, 222),
  (64763, 1948), (66788, 1025), (67162, 739), (70746, 1296), (71541, 862),
  (71955, 765), (72421, 915), (72633, 2171), (72779, 526), (72896, 1115),
  (73343, 1167), (78274, 2100), (78720, 2157)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X1Y0_check. -/
theorem Z0Split82A0X1Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X1Y0_pairs. -/
theorem Z0Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split82A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X1_pairs. -/
theorem Z0Split82A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split82A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0_pairs. -/
theorem Z0Split82A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split82A0X0_pairs x hx y hy hw
  · exact Z0Split82A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split82_check. -/
theorem Z0Split82_check : checkSplit m4TZ0 (4, 2, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split82A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split83A0X0Y0Certs : List (Nat × Nat) := [
  (3308, 135), (5732, 23), (5783, 1130), (7561, 12), (8759, 2088),
  (12368, 137), (12937, 109), (14398, 1926), (14433, 39), (15174, 1286),
  (15470, 828), (16304, 370), (16626, 83), (21047, 534), (21244, 53),
  (22052, 26), (22726, 477), (23046, 84), (23127, 1729), (23594, 371),
  (24094, 54), (26231, 225), (27484, 55), (29891, 226), (31454, 373),
  (32713, 313), (33773, 1132), (37359, 162), (38024, 374), (38923, 314),
  (40923, 42), (41828, 139), (42458, 140), (42547, 111), (43803, 43),
  (44305, 1448), (45530, 830), (46032, 260), (47657, 536), (48717, 1730),
  (49837, 113), (55553, 1133), (55929, 164), (56788, 1932), (57276, 89),
  (58252, 1019), (58752, 263), (58829, 2090), (59570, 831), (60279, 166)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X0Y0_check. -/
theorem Z0Split83A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X0Y0_pairs. -/
theorem Z0Split83A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split83A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X0_pairs. -/
theorem Z0Split83A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split83A0X1Y0Certs : List (Nat × Nat) := [
  (657, 1732), (1018, 1933), (1195, 1450), (1951, 16), (2717, 537),
  (3761, 228), (5270, 834), (6985, 1452), (7069, 729), (9379, 730),
  (14028, 617), (14655, 418), (15620, 835), (17578, 1935), (18474, 1292),
  (18529, 731), (21113, 1134), (22739, 2091), (24343, 318), (28165, 1453),
  (32367, 1735), (32925, 420), (34088, 146), (34646, 1564), (34812, 268),
  (35321, 230), (35988, 620), (37185, 421), (38061, 907), (38882, 31),
  (40794, 1294), (42481, 21), (46680, 3), (47905, 1454), (49067, 540),
  (50740, 202), (52198, 1937), (53820, 6), (54201, 910), (57569, 2094),
  (58281, 912), (58740, 8), (58934, 381), (59495, 77), (59808, 623)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X1Y0_check. -/
theorem Z0Split83A0X1Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split83A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X1Y0_pairs. -/
theorem Z0Split83A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split83A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split83A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X1_pairs. -/
theorem Z0Split83A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split83A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0_pairs. -/
theorem Z0Split83A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split83A0X0_pairs x hx y hy hw
  · exact Z0Split83A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split83_check. -/
theorem Z0Split83_check : checkSplit m4TZ0 (4, 3, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split83A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X0Y0_check. -/
theorem Z0Split84A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X0Y0_pairs. -/
theorem Z0Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X0_pairs. -/
theorem Z0Split84A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X1Y0_check. -/
theorem Z0Split84A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X1Y0_pairs. -/
theorem Z0Split84A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X1_pairs. -/
theorem Z0Split84A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X2Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X2Y0_check. -/
theorem Z0Split84A0X2Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X2Y0_pairs. -/
theorem Z0Split84A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X2Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk2 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X2_pairs. -/
theorem Z0Split84A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X3Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X3Y0_check. -/
theorem Z0Split84A0X3Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X3Y0_pairs. -/
theorem Z0Split84A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X3Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk3 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X3_pairs. -/
theorem Z0Split84A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X4Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X4Y0_check. -/
theorem Z0Split84A0X4Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X4Y0_pairs. -/
theorem Z0Split84A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X4Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk4 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X4_pairs. -/
theorem Z0Split84A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X5Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X5Y0_check. -/
theorem Z0Split84A0X5Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X5Y0_pairs. -/
theorem Z0Split84A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X5Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk5 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X5_pairs. -/
theorem Z0Split84A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X6Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X6Y0_check. -/
theorem Z0Split84A0X6Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X6Y0_pairs. -/
theorem Z0Split84A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X6Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk6 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X6_pairs. -/
theorem Z0Split84A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X7Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X7Y0_check. -/
theorem Z0Split84A0X7Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X7Y0_pairs. -/
theorem Z0Split84A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X7Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk7 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X7_pairs. -/
theorem Z0Split84A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X8Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X8Y0_check. -/
theorem Z0Split84A0X8Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X8Y0_pairs. -/
theorem Z0Split84A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X8Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk8 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X8_pairs. -/
theorem Z0Split84A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X9Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X9Y0_check. -/
theorem Z0Split84A0X9Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X9Y0_pairs. -/
theorem Z0Split84A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X9Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk9 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X9_pairs. -/
theorem Z0Split84A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X10Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X10Y0_check. -/
theorem Z0Split84A0X10Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X10Y0_pairs. -/
theorem Z0Split84A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X10Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk10 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X10_pairs. -/
theorem Z0Split84A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X11Y0_check. -/
theorem Z0Split84A0X11Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X11Y0_pairs. -/
theorem Z0Split84A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X11Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk11 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X11_pairs. -/
theorem Z0Split84A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X12Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X12Y0_check. -/
theorem Z0Split84A0X12Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X12Y0_pairs. -/
theorem Z0Split84A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X12Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk12 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X12_pairs. -/
theorem Z0Split84A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X13Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X13Y0_check. -/
theorem Z0Split84A0X13Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X13Y0_pairs. -/
theorem Z0Split84A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X13Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk13 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X13_pairs. -/
theorem Z0Split84A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X14Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X14Y0_check. -/
theorem Z0Split84A0X14Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X14Y0_pairs. -/
theorem Z0Split84A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X14Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk14 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X14_pairs. -/
theorem Z0Split84A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X15Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X15Y0_check. -/
theorem Z0Split84A0X15Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X15Y0_pairs. -/
theorem Z0Split84A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X15Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk15 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X15_pairs. -/
theorem Z0Split84A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X16Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X16Y0_check. -/
theorem Z0Split84A0X16Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X16Y0_pairs. -/
theorem Z0Split84A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X16Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk16 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X16_pairs. -/
theorem Z0Split84A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X17Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X17Y0_check. -/
theorem Z0Split84A0X17Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X17Y0_pairs. -/
theorem Z0Split84A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X17Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S2048Chunk17 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X17_pairs. -/
theorem Z0Split84A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0_pairs. -/
theorem Z0Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split84A0X0_pairs x hx y hy hw
  · exact Z0Split84A0X1_pairs x hx y hy hw
  · exact Z0Split84A0X2_pairs x hx y hy hw
  · exact Z0Split84A0X3_pairs x hx y hy hw
  · exact Z0Split84A0X4_pairs x hx y hy hw
  · exact Z0Split84A0X5_pairs x hx y hy hw
  · exact Z0Split84A0X6_pairs x hx y hy hw
  · exact Z0Split84A0X7_pairs x hx y hy hw
  · exact Z0Split84A0X8_pairs x hx y hy hw
  · exact Z0Split84A0X9_pairs x hx y hy hw
  · exact Z0Split84A0X10_pairs x hx y hy hw
  · exact Z0Split84A0X11_pairs x hx y hy hw
  · exact Z0Split84A0X12_pairs x hx y hy hw
  · exact Z0Split84A0X13_pairs x hx y hy hw
  · exact Z0Split84A0X14_pairs x hx y hy hw
  · exact Z0Split84A0X15_pairs x hx y hy hw
  · exact Z0Split84A0X16_pairs x hx y hy hw
  · exact Z0Split84A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split84_check. -/
theorem Z0Split84_check : checkSplit m4TZ0 (4, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split84A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split85A0X0Y0Certs : List (Nat × Nat) := [
  (179, 238), (211, 256), (691, 555), (734, 571), (804, 609),
  (1820, 1170), (1906, 1212), (2011, 1278)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0Y0_check. -/
theorem Z0Split85A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0Y0_pairs. -/
theorem Z0Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split85A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split85A0X0Y1Certs : List (Nat × Nat) := [
  (797, 1678), (1030, 1803), (1153, 1876), (1241, 1919), (1845, 2209),
  (1876, 2233), (1956, 2284)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0Y1_check. -/
theorem Z0Split85A0X0Y1_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split85A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0Y1_pairs. -/
theorem Z0Split85A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split85A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split85A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0_pairs. -/
theorem Z0Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split85A0X0Y0_pairs x hx y hy hw
  · exact Z0Split85A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0_pairs. -/
theorem Z0Split85A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split85A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split85_check. -/
theorem Z0Split85_check : checkSplit m4TZ0 (5, 0, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split85A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split86A0X0Y0Certs : List (Nat × Nat) := [
  (168, 682), (503, 275), (1080, 913), (1400, 385), (1899, 642),
  (2357, 776), (2612, 37), (3244, 855), (3812, 1583), (3834, 1743),
  (3981, 271), (4643, 1375), (5239, 102), (5970, 1492), (6173, 336),
  (6503, 2115), (6680, 631), (7216, 1148), (7905, 288), (8664, 2022),
  (8789, 360), (8881, 769), (9150, 95), (9928, 1758), (10469, 148),
  (11063, 810), (11167, 1367), (11729, 2148), (12414, 1030), (12479, 1437)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split86A0X0Y0_check. -/
theorem Z0Split86A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split86A0X0Y0_pairs. -/
theorem Z0Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split86A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split86A0X0_pairs. -/
theorem Z0Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split86A0_pairs. -/
theorem Z0Split86A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split86A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split86_check. -/
theorem Z0Split86_check : checkSplit m4TZ0 (5, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split86A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split87A0X0Y0Certs : List (Nat × Nat) := [
  (470, 825), (1460, 827), (1988, 136), (2065, 1442), (3718, 1927),
  (3835, 1445), (4664, 372), (4798, 1928), (5300, 829), (5485, 1447),
  (7148, 141), (7348, 1931), (7688, 142), (8444, 375), (8605, 1451),
  (8818, 1934), (10154, 378), (10328, 145), (10754, 379), (12590, 837)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0X0Y0_check. -/
theorem Z0Split87A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0X0Y0_pairs. -/
theorem Z0Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split87A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0X0_pairs. -/
theorem Z0Split87A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0_pairs. -/
theorem Z0Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split87_check. -/
theorem Z0Split87_check : checkSplit m4TZ0 (5, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split87A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split88A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X0Y0_check. -/
theorem Z0Split88A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X0Y0_pairs. -/
theorem Z0Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split88A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X0_pairs. -/
theorem Z0Split88A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split88A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X1Y0_check. -/
theorem Z0Split88A0X1Y0_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split88A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X1Y0_pairs. -/
theorem Z0Split88A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split88A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split88A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X1_pairs. -/
theorem Z0Split88A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split88A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0_pairs. -/
theorem Z0Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split88A0X0_pairs x hx y hy hw
  · exact Z0Split88A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split88_check. -/
theorem Z0Split88_check : checkSplit m4TZ0 (5, 3, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split88A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split89A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split89A0X0Y0_check. -/
theorem Z0Split89A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split89A0X0Y0_pairs. -/
theorem Z0Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split89A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split89A0X0_pairs. -/
theorem Z0Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split89A0_pairs. -/
theorem Z0Split89A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split89A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split89_check. -/
theorem Z0Split89_check : checkSplit m4TZ0 (6, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split89A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split90A0X0Y0Certs : List (Nat × Nat) := [
  (12, 259), (38, 134), (52, 1016), (78, 614), (134, 369),
  (146, 1560), (180, 0), (259, 726), (275, 70), (290, 826),
  (362, 24), (444, 1285), (460, 195), (475, 1443), (546, 86),
  (603, 40), (646, 479), (658, 1929), (757, 114), (853, 319)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0X0Y0_check. -/
theorem Z0Split90A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0X0Y0_pairs. -/
theorem Z0Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split90A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0X0_pairs. -/
theorem Z0Split90A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0_pairs. -/
theorem Z0Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split90_check. -/
theorem Z0Split90_check : checkSplit m4TZ0 (6, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split90A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0X0Y0_check. -/
theorem Z0Split91A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0X0Y0_pairs. -/
theorem Z0Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split91A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0X0_pairs. -/
theorem Z0Split91A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0_pairs. -/
theorem Z0Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split91_check. -/
theorem Z0Split91_check : checkSplit m4TZ0 (6, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split91A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0X0Y0_check. -/
theorem Z0Split92A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0X0Y0_pairs. -/
theorem Z0Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split92A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0X0_pairs. -/
theorem Z0Split92A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0_pairs. -/
theorem Z0Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split92_check. -/
theorem Z0Split92_check : checkSplit m4TZ0 (7, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split92A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0X0Y0_check. -/
theorem Z0Split93A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0X0Y0_pairs. -/
theorem Z0Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split93A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0X0_pairs. -/
theorem Z0Split93A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0_pairs. -/
theorem Z0Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split93_check. -/
theorem Z0Split93_check : checkSplit m4TZ0 (7, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split93A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0X0Y0_check. -/
theorem Z0Split94A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0X0Y0_pairs. -/
theorem Z0Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 8 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split94A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0X0_pairs. -/
theorem Z0Split94A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 8 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0_pairs. -/
theorem Z0Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 8 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split94_check. -/
theorem Z0Split94_check : checkSplit m4TZ0 (8, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split94A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

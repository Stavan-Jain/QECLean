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
def Z1Split80A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y0_check. -/
theorem Z1Split80A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y0_pairs. -/
theorem Z1Split80A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk0_bound y hy)
  · exact Z1Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y1Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y1_check. -/
theorem Z1Split80A0X0Y1_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y1_pairs. -/
theorem Z1Split80A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk1_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk1_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk1_bound y hy)
  · exact Z1Split80A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y2Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y2_check. -/
theorem Z1Split80A0X0Y2_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y2_pairs. -/
theorem Z1Split80A0X0Y2_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y2Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk2_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk2
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk2_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk2_bound y hy)
  · exact Z1Split80A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y3Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y3_check. -/
theorem Z1Split80A0X0Y3_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y3_pairs. -/
theorem Z1Split80A0X0Y3_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y3Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk3_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk3
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk3_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk3_bound y hy)
  · exact Z1Split80A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y4Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y4_check. -/
theorem Z1Split80A0X0Y4_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y4_pairs. -/
theorem Z1Split80A0X0Y4_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y4Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk4_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk4
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk4_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk4_bound y hy)
  · exact Z1Split80A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y5Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y5_check. -/
theorem Z1Split80A0X0Y5_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y5_pairs. -/
theorem Z1Split80A0X0Y5_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y5Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk5_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk5
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk5_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk5_bound y hy)
  · exact Z1Split80A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y6Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y6_check. -/
theorem Z1Split80A0X0Y6_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y6_pairs. -/
theorem Z1Split80A0X0Y6_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y6Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk6_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk6
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk6_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk6_bound y hy)
  · exact Z1Split80A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y7Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y7_check. -/
theorem Z1Split80A0X0Y7_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y7_pairs. -/
theorem Z1Split80A0X0Y7_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y7Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk7_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk7
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk7_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk7_bound y hy)
  · exact Z1Split80A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y8Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y8_check. -/
theorem Z1Split80A0X0Y8_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y8_pairs. -/
theorem Z1Split80A0X0Y8_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk8,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y8Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk8_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk8_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk8
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk8_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk8_bound y hy)
  · exact Z1Split80A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y9Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y9_check. -/
theorem Z1Split80A0X0Y9_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y9_pairs. -/
theorem Z1Split80A0X0Y9_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk9,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y9Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk9_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk9_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk9
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk9_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk9_bound y hy)
  · exact Z1Split80A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y10Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y10_check. -/
theorem Z1Split80A0X0Y10_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y10_pairs. -/
theorem Z1Split80A0X0Y10_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk10,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y10Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk10_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk10_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk10
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk10_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk10_bound y hy)
  · exact Z1Split80A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y11Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y11_check. -/
theorem Z1Split80A0X0Y11_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y11Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y11_pairs. -/
theorem Z1Split80A0X0Y11_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk11,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y11Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk11_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk11_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk11
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk11_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk11_bound y hy)
  · exact Z1Split80A0X0Y11_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y12Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y12_check. -/
theorem Z1Split80A0X0Y12_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y12Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y12_pairs. -/
theorem Z1Split80A0X0Y12_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk12,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y12Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk12_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk12_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk12
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk12_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk12_bound y hy)
  · exact Z1Split80A0X0Y12_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y13Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y13_check. -/
theorem Z1Split80A0X0Y13_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y13Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y13_pairs. -/
theorem Z1Split80A0X0Y13_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk13,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y13Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk13_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk13_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk13
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk13_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk13_bound y hy)
  · exact Z1Split80A0X0Y13_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y14Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y14_check. -/
theorem Z1Split80A0X0Y14_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y14Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y14_pairs. -/
theorem Z1Split80A0X0Y14_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk14,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y14Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk14_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk14_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk14
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk14_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk14_bound y hy)
  · exact Z1Split80A0X0Y14_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y15Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y15_check. -/
theorem Z1Split80A0X0Y15_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y15Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y15_pairs. -/
theorem Z1Split80A0X0Y15_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk15,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y15Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk15_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk15_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk15
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk15_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk15_bound y hy)
  · exact Z1Split80A0X0Y15_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y16Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y16_check. -/
theorem Z1Split80A0X0Y16_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y16Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y16_pairs. -/
theorem Z1Split80A0X0Y16_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk16,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y16Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk16_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk16_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk16
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk16_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk16_bound y hy)
  · exact Z1Split80A0X0Y16_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y17Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y17_check. -/
theorem Z1Split80A0X0Y17_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y17Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y17_pairs. -/
theorem Z1Split80A0X0Y17_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk17,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y17Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk17_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S2048Chunk17_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S2048Chunk17
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk17_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks4S2048Chunk17_bound y hy)
  · exact Z1Split80A0X0Y17_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0_pairs. -/
theorem Z1Split80A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split80A0X0Y0_pairs x hx y hy hw
  · exact Z1Split80A0X0Y1_pairs x hx y hy hw
  · exact Z1Split80A0X0Y2_pairs x hx y hy hw
  · exact Z1Split80A0X0Y3_pairs x hx y hy hw
  · exact Z1Split80A0X0Y4_pairs x hx y hy hw
  · exact Z1Split80A0X0Y5_pairs x hx y hy hw
  · exact Z1Split80A0X0Y6_pairs x hx y hy hw
  · exact Z1Split80A0X0Y7_pairs x hx y hy hw
  · exact Z1Split80A0X0Y8_pairs x hx y hy hw
  · exact Z1Split80A0X0Y9_pairs x hx y hy hw
  · exact Z1Split80A0X0Y10_pairs x hx y hy hw
  · exact Z1Split80A0X0Y11_pairs x hx y hy hw
  · exact Z1Split80A0X0Y12_pairs x hx y hy hw
  · exact Z1Split80A0X0Y13_pairs x hx y hy hw
  · exact Z1Split80A0X0Y14_pairs x hx y hy hw
  · exact Z1Split80A0X0Y15_pairs x hx y hy hw
  · exact Z1Split80A0X0Y16_pairs x hx y hy hw
  · exact Z1Split80A0X0Y17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0_pairs. -/
theorem Z1Split80A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split80A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split80_check. -/
theorem Z1Split80_check : checkSplit m4TZ1 (4, 0, 4, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split80A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split81A0X0Y0Certs : List (Nat × Nat) := [
  (2496, 544), (4917, 814), (8031, 1603), (9498, 1212), (10547, 500),
  (10663, 577), (12795, 650), (16322, 232), (16416, 333), (17261, 942),
  (19099, 837), (21530, 1129), (21757, 1284), (25505, 1054), (26020, 1411),
  (28943, 625), (29177, 805), (31182, 796), (32734, 433), (35159, 735),
  (40802, 400), (42146, 1380), (42589, 195), (45648, 996), (47757, 1050),
  (48486, 1572), (49345, 753), (51676, 949), (52734, 210), (56990, 393)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0Y0_check. -/
theorem Z1Split81A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0Y0_pairs. -/
theorem Z1Split81A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split81A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z1Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split81A0X0Y1Certs : List (Nat × Nat) := [
  (1323, 2638), (1505, 2773), (5003, 2377), (11085, 2359), (13943, 3015),
  (15452, 2556), (22015, 2967), (23033, 2141), (23630, 2570), (28452, 3181),
  (28709, 1762), (32808, 1810), (33125, 2047), (36338, 3014), (37094, 1936),
  (37530, 2301), (40376, 2991), (41209, 1967), (45377, 2100), (46420, 2922),
  (51719, 2252), (52174, 2604), (53210, 1834), (54952, 3236), (55400, 1930),
  (55993, 2423), (57224, 1771), (57742, 2200), (60571, 2777), (60907, 3100)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0Y1_check. -/
theorem Z1Split81A0X0Y1_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split81A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0Y1_pairs. -/
theorem Z1Split81A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split81A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z1Split81A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0_pairs. -/
theorem Z1Split81A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split81A0X0Y0_pairs x hx y hy hw
  · exact Z1Split81A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0_pairs. -/
theorem Z1Split81A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split81A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split81_check. -/
theorem Z1Split81_check : checkSplit m4TZ1 (4, 1, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split81A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split82A0X0Y0Certs : List (Nat × Nat) := [
  (1576, 1566), (7011, 236), (10356, 2348), (12203, 125), (13080, 156),
  (14359, 50), (14689, 2128), (14746, 2640), (14863, 347), (18185, 2296),
  (19183, 205), (20133, 597), (20981, 477), (24167, 1347), (24225, 1843),
  (24772, 2959), (24886, 443), (26240, 693), (26641, 532), (30582, 636),
  (32264, 349), (33673, 904), (36187, 375), (36948, 2947), (37810, 2740),
  (40121, 479), (40539, 382), (41081, 1009), (42292, 454), (43960, 134),
  (44045, 541), (44114, 907), (44971, 847), (46000, 2089), (49335, 911),
  (50408, 2595), (51883, 569), (53782, 1633), (54178, 1321), (55451, 1088),
  (57116, 634), (59225, 306), (60372, 2192), (60410, 2586), (60977, 354),
  (61476, 697), (61962, 1013), (63772, 1492), (64594, 1177), (70719, 1396),
  (71751, 2957), (72812, 852), (74239, 1679), (76678, 570), (78915, 912),
  (79559, 2634), (79666, 290), (80808, 2118), (82840, 1008), (83298, 1172),
  (84596, 1091), (85443, 926), (85999, 1849), (88072, 1051), (89697, 396),
  (89830, 1202), (89900, 1687), (90651, 888), (92232, 79), (93811, 1669),
  (94863, 164), (97731, 1697), (98363, 246), (100279, 1268), (101054, 648),
  (102003, 1173), (103539, 64), (104738, 2147), (105497, 1257), (106462, 1984),
  (108128, 1392)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X0Y0_check. -/
theorem Z1Split82A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X0Y0_pairs. -/
theorem Z1Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split82A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X0_pairs. -/
theorem Z1Split82A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split82A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split82A0X1Y0Certs : List (Nat × Nat) := [
  (174, 894), (1022, 767), (1572, 1523), (2530, 2361), (2644, 173),
  (2868, 1475), (4085, 864), (4613, 1496), (5526, 1856), (7326, 2418),
  (7867, 193), (12213, 165), (13709, 1221), (14584, 1269), (17256, 1699),
  (17544, 709), (17983, 732), (18801, 451), (20723, 1637), (21157, 1635),
  (21617, 1846), (21950, 1038), (22207, 121), (24682, 1987), (25959, 1733),
  (26487, 2623), (28593, 1931), (30136, 596), (30201, 947), (30208, 1015),
  (33311, 1410), (34387, 122), (36441, 2139), (37018, 208), (38021, 902),
  (38969, 1463), (39989, 2832), (41673, 2271), (42739, 540), (43783, 1652),
  (45161, 2364), (45515, 1621), (46046, 2479), (47395, 2972), (47953, 503),
  (48211, 2380), (49408, 1462), (49957, 2422), (50850, 2637), (52627, 3093),
  (54753, 2584), (55263, 111), (56124, 66), (57369, 2601), (57736, 1911),
  (58372, 378), (61304, 2835), (62208, 49), (62753, 551), (65920, 1316),
  (65982, 1769), (65992, 1858), (66716, 807), (67644, 1197), (69246, 374),
  (71321, 2977), (72152, 2568), (72641, 3153), (73631, 565), (74593, 1135),
  (74807, 3023), (76043, 2355), (76553, 3099), (77921, 279)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X1Y0_check. -/
theorem Z1Split82A0X1Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X1Y0_pairs. -/
theorem Z1Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split82A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X1_pairs. -/
theorem Z1Split82A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split82A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0_pairs. -/
theorem Z1Split82A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split82A0X0_pairs x hx y hy hw
  · exact Z1Split82A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split82_check. -/
theorem Z1Split82_check : checkSplit m4TZ1 (4, 2, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split82A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split83A0X0Y0Certs : List (Nat × Nat) := [
  (660, 0), (4409, 2929), (7172, 21), (11898, 773), (15262, 1301),
  (19451, 262), (26736, 90), (27642, 313), (31975, 1835), (37200, 6),
  (39948, 774), (43946, 2083), (51827, 672), (51935, 70), (57311, 265)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X0Y0_check. -/
theorem Z1Split83A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X0Y0_pairs. -/
theorem Z1Split83A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split83A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X0_pairs. -/
theorem Z1Split83A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split83A0X1Y0Certs : List (Nat × Nat) := [
  (4439, 2936), (6028, 2580), (11978, 151), (14432, 28), (17697, 2341),
  (19880, 1002), (26243, 1455), (26410, 222), (34847, 677), (38442, 322),
  (38806, 591), (44714, 441), (47196, 99), (54387, 2346), (59843, 1459)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X1Y0_check. -/
theorem Z1Split83A0X1Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split83A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X1Y0_pairs. -/
theorem Z1Split83A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split83A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split83A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X1_pairs. -/
theorem Z1Split83A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split83A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0_pairs. -/
theorem Z1Split83A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split83A0X0_pairs x hx y hy hw
  · exact Z1Split83A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split83_check. -/
theorem Z1Split83_check : checkSplit m4TZ1 (4, 3, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split83A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X0Y0_check. -/
theorem Z1Split84A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X0Y0_pairs. -/
theorem Z1Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X0_pairs. -/
theorem Z1Split84A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X1Y0_check. -/
theorem Z1Split84A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X1Y0_pairs. -/
theorem Z1Split84A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X1_pairs. -/
theorem Z1Split84A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X2Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X2Y0_check. -/
theorem Z1Split84A0X2Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X2Y0_pairs. -/
theorem Z1Split84A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X2Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk2 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X2_pairs. -/
theorem Z1Split84A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X3Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X3Y0_check. -/
theorem Z1Split84A0X3Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X3Y0_pairs. -/
theorem Z1Split84A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X3Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk3 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X3_pairs. -/
theorem Z1Split84A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X4Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X4Y0_check. -/
theorem Z1Split84A0X4Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X4Y0_pairs. -/
theorem Z1Split84A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X4Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk4 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X4_pairs. -/
theorem Z1Split84A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X5Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X5Y0_check. -/
theorem Z1Split84A0X5Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X5Y0_pairs. -/
theorem Z1Split84A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X5Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk5 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X5_pairs. -/
theorem Z1Split84A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X6Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X6Y0_check. -/
theorem Z1Split84A0X6Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X6Y0_pairs. -/
theorem Z1Split84A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X6Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk6 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X6_pairs. -/
theorem Z1Split84A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X7Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X7Y0_check. -/
theorem Z1Split84A0X7Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X7Y0_pairs. -/
theorem Z1Split84A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X7Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk7 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X7_pairs. -/
theorem Z1Split84A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X8Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X8Y0_check. -/
theorem Z1Split84A0X8Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X8Y0_pairs. -/
theorem Z1Split84A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X8Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk8 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X8_pairs. -/
theorem Z1Split84A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X9Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X9Y0_check. -/
theorem Z1Split84A0X9Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X9Y0_pairs. -/
theorem Z1Split84A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X9Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk9 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X9_pairs. -/
theorem Z1Split84A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X10Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X10Y0_check. -/
theorem Z1Split84A0X10Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X10Y0_pairs. -/
theorem Z1Split84A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X10Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk10 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X10_pairs. -/
theorem Z1Split84A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X11Y0_check. -/
theorem Z1Split84A0X11Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X11Y0_pairs. -/
theorem Z1Split84A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X11Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk11 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X11_pairs. -/
theorem Z1Split84A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X12Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X12Y0_check. -/
theorem Z1Split84A0X12Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X12Y0_pairs. -/
theorem Z1Split84A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X12Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk12 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X12_pairs. -/
theorem Z1Split84A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X13Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X13Y0_check. -/
theorem Z1Split84A0X13Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X13Y0_pairs. -/
theorem Z1Split84A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X13Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk13 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X13_pairs. -/
theorem Z1Split84A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X14Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X14Y0_check. -/
theorem Z1Split84A0X14Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X14Y0_pairs. -/
theorem Z1Split84A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X14Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk14 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X14_pairs. -/
theorem Z1Split84A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X15Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X15Y0_check. -/
theorem Z1Split84A0X15Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X15Y0_pairs. -/
theorem Z1Split84A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X15Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk15 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X15_pairs. -/
theorem Z1Split84A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X16Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X16Y0_check. -/
theorem Z1Split84A0X16Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X16Y0_pairs. -/
theorem Z1Split84A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X16Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk16 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X16_pairs. -/
theorem Z1Split84A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X17Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X17Y0_check. -/
theorem Z1Split84A0X17Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X17Y0_pairs. -/
theorem Z1Split84A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X17Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S2048Chunk17 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X17_pairs. -/
theorem Z1Split84A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0_pairs. -/
theorem Z1Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split84A0X0_pairs x hx y hy hw
  · exact Z1Split84A0X1_pairs x hx y hy hw
  · exact Z1Split84A0X2_pairs x hx y hy hw
  · exact Z1Split84A0X3_pairs x hx y hy hw
  · exact Z1Split84A0X4_pairs x hx y hy hw
  · exact Z1Split84A0X5_pairs x hx y hy hw
  · exact Z1Split84A0X6_pairs x hx y hy hw
  · exact Z1Split84A0X7_pairs x hx y hy hw
  · exact Z1Split84A0X8_pairs x hx y hy hw
  · exact Z1Split84A0X9_pairs x hx y hy hw
  · exact Z1Split84A0X10_pairs x hx y hy hw
  · exact Z1Split84A0X11_pairs x hx y hy hw
  · exact Z1Split84A0X12_pairs x hx y hy hw
  · exact Z1Split84A0X13_pairs x hx y hy hw
  · exact Z1Split84A0X14_pairs x hx y hy hw
  · exact Z1Split84A0X15_pairs x hx y hy hw
  · exact Z1Split84A0X16_pairs x hx y hy hw
  · exact Z1Split84A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split84_check. -/
theorem Z1Split84_check : checkSplit m4TZ1 (4, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split84A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split85A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0Y0_check. -/
theorem Z1Split85A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0Y0_pairs. -/
theorem Z1Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split85A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z1Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split85A0X0Y1Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0Y1_check. -/
theorem Z1Split85A0X0Y1_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split85A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0Y1_pairs. -/
theorem Z1Split85A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split85A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z1Split85A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0_pairs. -/
theorem Z1Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split85A0X0Y0_pairs x hx y hy hw
  · exact Z1Split85A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0_pairs. -/
theorem Z1Split85A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split85A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split85_check. -/
theorem Z1Split85_check : checkSplit m4TZ1 (5, 0, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split85A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split86A0X0Y0Certs : List (Nat × Nat) := [
  (259, 1476), (1233, 2390), (2513, 2146), (3034, 3039), (3867, 2622),
  (4526, 899), (5044, 1477), (5275, 275), (6203, 548), (7246, 1668),
  (7758, 2391), (7968, 688), (8924, 1220), (9693, 599), (10429, 3040),
  (11066, 1012), (11548, 1324), (11800, 276), (12484, 1852), (12753, 690)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split86A0X0Y0_check. -/
theorem Z1Split86A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split86A0X0Y0_pairs. -/
theorem Z1Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split86A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split86A0X0_pairs. -/
theorem Z1Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split86A0_pairs. -/
theorem Z1Split86A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split86A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split86_check. -/
theorem Z1Split86_check : checkSplit m4TZ1 (5, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split86A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split87A0X0Y0Certs : List (Nat × Nat) := [
  (33, 40), (517, 114), (912, 311), (1044, 1627), (1853, 1446),
  (2173, 362), (2310, 1), (2928, 772), (3093, 42), (4257, 2336),
  (4411, 15), (4467, 2337), (4614, 1628), (4969, 881), (5102, 24),
  (6060, 5), (6247, 117), (7269, 185), (7596, 92), (7761, 1159),
  (7919, 2933), (8104, 56), (8159, 2935), (9013, 365), (9542, 27),
  (10103, 1454), (10275, 525), (10541, 268), (10602, 319), (10831, 18),
  (11021, 269), (11229, 189), (11346, 98), (11419, 885), (12257, 680),
  (12378, 782), (12531, 1164), (12664, 59), (12857, 683), (13005, 529)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0X0Y0_check. -/
theorem Z1Split87A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0X0Y0_pairs. -/
theorem Z1Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split87A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0X0_pairs. -/
theorem Z1Split87A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0_pairs. -/
theorem Z1Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split87_check. -/
theorem Z1Split87_check : checkSplit m4TZ1 (5, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split87A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split88A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X0Y0_check. -/
theorem Z1Split88A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X0Y0_pairs. -/
theorem Z1Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split88A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X0_pairs. -/
theorem Z1Split88A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split88A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X1Y0_check. -/
theorem Z1Split88A0X1Y0_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split88A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X1Y0_pairs. -/
theorem Z1Split88A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split88A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split88A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X1_pairs. -/
theorem Z1Split88A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split88A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0_pairs. -/
theorem Z1Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split88A0X0_pairs x hx y hy hw
  · exact Z1Split88A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split88_check. -/
theorem Z1Split88_check : checkSplit m4TZ1 (5, 3, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split88A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split89A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split89A0X0Y0_check. -/
theorem Z1Split89A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split89A0X0Y0_pairs. -/
theorem Z1Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split89A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split89A0X0_pairs. -/
theorem Z1Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split89A0_pairs. -/
theorem Z1Split89A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split89A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split89_check. -/
theorem Z1Split89_check : checkSplit m4TZ1 (6, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split89A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split90A0X0Y0Certs : List (Nat × Nat) := [
  (162, 310), (267, 2334), (318, 771), (449, 2930), (480, 3),
  (611, 263), (662, 26), (767, 673), (786, 96), (863, 1456)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0X0Y0_check. -/
theorem Z1Split90A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0X0Y0_pairs. -/
theorem Z1Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split90A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0X0_pairs. -/
theorem Z1Split90A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0_pairs. -/
theorem Z1Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split90_check. -/
theorem Z1Split90_check : checkSplit m4TZ1 (6, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split90A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0X0Y0_check. -/
theorem Z1Split91A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0X0Y0_pairs. -/
theorem Z1Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split91A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0X0_pairs. -/
theorem Z1Split91A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0_pairs. -/
theorem Z1Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split91_check. -/
theorem Z1Split91_check : checkSplit m4TZ1 (6, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split91A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0X0Y0_check. -/
theorem Z1Split92A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0X0Y0_pairs. -/
theorem Z1Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split92A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0X0_pairs. -/
theorem Z1Split92A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0_pairs. -/
theorem Z1Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split92_check. -/
theorem Z1Split92_check : checkSplit m4TZ1 (7, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split92A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0X0Y0_check. -/
theorem Z1Split93A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0X0Y0_pairs. -/
theorem Z1Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split93A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0X0_pairs. -/
theorem Z1Split93A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0_pairs. -/
theorem Z1Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split93_check. -/
theorem Z1Split93_check : checkSplit m4TZ1 (7, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split93A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0X0Y0_check. -/
theorem Z1Split94A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0X0Y0_pairs. -/
theorem Z1Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 8 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split94A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0X0_pairs. -/
theorem Z1Split94A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 8 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0_pairs. -/
theorem Z1Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 8 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split94_check. -/
theorem Z1Split94_check : checkSplit m4TZ1 (8, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split94A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

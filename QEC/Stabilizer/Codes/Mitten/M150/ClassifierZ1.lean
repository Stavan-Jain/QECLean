/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.MaskChunks
import QEC.Stabilizer.Codes.Mitten.M150.SweepMaps
import QEC.Stabilizer.Codes.Mitten.M150.PackedGridSweep

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split0A0X0Y0Certs : List (Nat × Nat) := [
  (0, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split0A0X0Y0_check. -/
theorem Z1Split0A0X0Y0_check : checkGrid m4TZ1 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split0A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split0A0X0Y0_pairs. -/
theorem Z1Split0A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 0 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split0A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split0A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split0A0X0_pairs. -/
theorem Z1Split0A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 0 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split0A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split0A0_pairs. -/
theorem Z1Split0A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 0 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split0A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split0_check. -/
theorem Z1Split0_check : checkSplit m4TZ1 (0, 0, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split0A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split1A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split1A0X0Y0_check. -/
theorem Z1Split1A0X0Y0_check : checkGrid m4TZ1 3 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split1A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split1A0X0Y0_pairs. -/
theorem Z1Split1A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 2 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split1A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split1A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split1A0X0_pairs. -/
theorem Z1Split1A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 2 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split1A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split1A0_pairs. -/
theorem Z1Split1A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 2 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split1A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split1_check. -/
theorem Z1Split1_check : checkSplit m4TZ1 (0, 0, 2, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split1A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split2A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split2A0X0Y0_check. -/
theorem Z1Split2A0X0Y0_check : checkGrid m4TZ1 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split2A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split2A0X0Y0_pairs. -/
theorem Z1Split2A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 1 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split2A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split2A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split2A0X0_pairs. -/
theorem Z1Split2A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 1 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split2A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split2A0_pairs. -/
theorem Z1Split2A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 1 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split2A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split2_check. -/
theorem Z1Split2_check : checkSplit m4TZ1 (0, 1, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split2A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split3A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split3A0X0Y0_check. -/
theorem Z1Split3A0X0Y0_check : checkGrid m4TZ1 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split3A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split3A0X0Y0_pairs. -/
theorem Z1Split3A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split3A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split3A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split3A0X0_pairs. -/
theorem Z1Split3A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split3A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split3A0_pairs. -/
theorem Z1Split3A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split3A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split3_check. -/
theorem Z1Split3_check : checkSplit m4TZ1 (0, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split3A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split4A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split4A0X0Y0_check. -/
theorem Z1Split4A0X0Y0_check : checkGrid m4TZ1 2 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split4A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split4A0X0Y0_pairs. -/
theorem Z1Split4A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 1 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split4A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split4A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split4A0X0_pairs. -/
theorem Z1Split4A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 1 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split4A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split4A0_pairs. -/
theorem Z1Split4A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 1 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split4A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split4_check. -/
theorem Z1Split4_check : checkSplit m4TZ1 (1, 0, 1, 2) = true := by
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
    · exact Z1Split4A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split5A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split5A0X0Y0_check. -/
theorem Z1Split5A0X0Y0_check : checkGrid m4TZ1 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split5A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split5A0X0Y0_pairs. -/
theorem Z1Split5A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 1 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split5A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split5A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split5A0X0_pairs. -/
theorem Z1Split5A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 1 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split5A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split5A0_pairs. -/
theorem Z1Split5A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 1 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split5A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split5_check. -/
theorem Z1Split5_check : checkSplit m4TZ1 (1, 1, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split5A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split6A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split6A0X0Y0_check. -/
theorem Z1Split6A0X0Y0_check : checkGrid m4TZ1 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split6A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split6A0X0Y0_pairs. -/
theorem Z1Split6A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split6A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split6A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split6A0X0_pairs. -/
theorem Z1Split6A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split6A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split6A0_pairs. -/
theorem Z1Split6A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split6A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split6_check. -/
theorem Z1Split6_check : checkSplit m4TZ1 (2, 0, 0, 2) = true := by
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
    · exact Z1Split6A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split7A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split7A0X0Y0_check. -/
theorem Z1Split7A0X0Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split7A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split7A0X0Y0_pairs. -/
theorem Z1Split7A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split7A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split7A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split7A0X0_pairs. -/
theorem Z1Split7A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split7A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split7A0_pairs. -/
theorem Z1Split7A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split7A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split7_check. -/
theorem Z1Split7_check : checkSplit m4TZ1 (0, 0, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split7A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split8A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split8A0X0Y0_check. -/
theorem Z1Split8A0X0Y0_check : checkGrid m4TZ1 3 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split8A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split8A0X0Y0_pairs. -/
theorem Z1Split8A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split8A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split8A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split8A0X0_pairs. -/
theorem Z1Split8A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split8A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split8A0_pairs. -/
theorem Z1Split8A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split8A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split8_check. -/
theorem Z1Split8_check : checkSplit m4TZ1 (0, 1, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split8A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split9A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split9A0X0Y0_check. -/
theorem Z1Split9A0X0Y0_check : checkGrid m4TZ1 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split9A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split9A0X0Y0_pairs. -/
theorem Z1Split9A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split9A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split9A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split9A0X0_pairs. -/
theorem Z1Split9A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split9A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split9A0_pairs. -/
theorem Z1Split9A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split9A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split9_check. -/
theorem Z1Split9_check : checkSplit m4TZ1 (0, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split9A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split10A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split10A0X0Y0_check. -/
theorem Z1Split10A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split10A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split10A0X0Y0_pairs. -/
theorem Z1Split10A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split10A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split10A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split10A0X0_pairs. -/
theorem Z1Split10A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split10A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split10A0_pairs. -/
theorem Z1Split10A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split10A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split10_check. -/
theorem Z1Split10_check : checkSplit m4TZ1 (0, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split10A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split11A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split11A0X0Y0_check. -/
theorem Z1Split11A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split11A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split11A0X0Y0_pairs. -/
theorem Z1Split11A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split11A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split11A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split11A0X0_pairs. -/
theorem Z1Split11A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split11A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split11A0_pairs. -/
theorem Z1Split11A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split11A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split11_check. -/
theorem Z1Split11_check : checkSplit m4TZ1 (0, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split11A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split12A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split12A0X0Y0_check. -/
theorem Z1Split12A0X0Y0_check : checkGrid m4TZ1 3 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split12A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split12A0X0Y0_pairs. -/
theorem Z1Split12A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split12A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split12A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split12A0X0_pairs. -/
theorem Z1Split12A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split12A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split12A0_pairs. -/
theorem Z1Split12A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split12A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split12_check. -/
theorem Z1Split12_check : checkSplit m4TZ1 (1, 0, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split12A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split13A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split13A0X0Y0_check. -/
theorem Z1Split13A0X0Y0_check : checkGrid m4TZ1 3 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split13A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split13A0X0Y0_pairs. -/
theorem Z1Split13A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 2 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split13A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split13A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split13A0X0_pairs. -/
theorem Z1Split13A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 2 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split13A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split13A0_pairs. -/
theorem Z1Split13A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 2 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split13A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split13_check. -/
theorem Z1Split13_check : checkSplit m4TZ1 (1, 1, 2, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split13A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split14A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split14A0X0Y0_check. -/
theorem Z1Split14A0X0Y0_check : checkGrid m4TZ1 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split14A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split14A0X0Y0_pairs. -/
theorem Z1Split14A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split14A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split14A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split14A0X0_pairs. -/
theorem Z1Split14A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split14A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split14A0_pairs. -/
theorem Z1Split14A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split14A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split14_check. -/
theorem Z1Split14_check : checkSplit m4TZ1 (1, 2, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split14A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split15A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split15A0X0Y0_check. -/
theorem Z1Split15A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split15A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split15A0X0Y0_pairs. -/
theorem Z1Split15A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split15A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split15A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split15A0X0_pairs. -/
theorem Z1Split15A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split15A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split15A0_pairs. -/
theorem Z1Split15A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split15A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split15_check. -/
theorem Z1Split15_check : checkSplit m4TZ1 (1, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split15A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split16A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0X0Y0_check. -/
theorem Z1Split16A0X0Y0_check : checkGrid m4TZ1 2 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split16A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0X0Y0_pairs. -/
theorem Z1Split16A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split16A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
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
      exact Z1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split16A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0X0_pairs. -/
theorem Z1Split16A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split16A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0_pairs. -/
theorem Z1Split16A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split16A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split16_check. -/
theorem Z1Split16_check : checkSplit m4TZ1 (2, 0, 2, 2) = true := by
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
    · exact Z1Split16A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split17A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0X0Y0_check. -/
theorem Z1Split17A0X0Y0_check : checkGrid m4TZ1 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split17A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0X0Y0_pairs. -/
theorem Z1Split17A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split17A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split17A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0X0_pairs. -/
theorem Z1Split17A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split17A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0_pairs. -/
theorem Z1Split17A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split17A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split17_check. -/
theorem Z1Split17_check : checkSplit m4TZ1 (2, 1, 1, 2) = true := by
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
    · exact Z1Split17A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split18A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0X0Y0_check. -/
theorem Z1Split18A0X0Y0_check : checkGrid m4TZ1 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split18A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0X0Y0_pairs. -/
theorem Z1Split18A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split18A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split18A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0X0_pairs. -/
theorem Z1Split18A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split18A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0_pairs. -/
theorem Z1Split18A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split18A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split18_check. -/
theorem Z1Split18_check : checkSplit m4TZ1 (2, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split18A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split19A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0X0Y0_check. -/
theorem Z1Split19A0X0Y0_check : checkGrid m4TZ1 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split19A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0X0Y0_pairs. -/
theorem Z1Split19A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split19A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split19A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0X0_pairs. -/
theorem Z1Split19A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split19A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0_pairs. -/
theorem Z1Split19A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split19A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split19_check. -/
theorem Z1Split19_check : checkSplit m4TZ1 (3, 0, 1, 2) = true := by
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
    · exact Z1Split19A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split20A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0X0Y0_check. -/
theorem Z1Split20A0X0Y0_check : checkGrid m4TZ1 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split20A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0X0Y0_pairs. -/
theorem Z1Split20A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split20A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split20A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0X0_pairs. -/
theorem Z1Split20A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split20A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0_pairs. -/
theorem Z1Split20A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split20A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split20_check. -/
theorem Z1Split20_check : checkSplit m4TZ1 (3, 1, 0, 2) = true := by
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
    · exact Z1Split20A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split21A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0X0Y0_check. -/
theorem Z1Split21A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split21A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0X0Y0_pairs. -/
theorem Z1Split21A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split21A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split21A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0X0_pairs. -/
theorem Z1Split21A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split21A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0_pairs. -/
theorem Z1Split21A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split21A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split21_check. -/
theorem Z1Split21_check : checkSplit m4TZ1 (4, 0, 0, 2) = true := by
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
    · exact Z1Split21A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split22A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0X0Y0_check. -/
theorem Z1Split22A0X0Y0_check : checkGrid m4TZ1 3 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split22A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0X0Y0_pairs. -/
theorem Z1Split22A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split22A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split22A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0X0_pairs. -/
theorem Z1Split22A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split22A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0_pairs. -/
theorem Z1Split22A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split22A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split22_check. -/
theorem Z1Split22_check : checkSplit m4TZ1 (0, 0, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split22A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split23A0X0Y0Certs : List (Nat × Nat) := [
  (0, 2442), (2, 3137), (6, 2457), (11, 2521), (12, 3035),
  (17, 3215), (18, 1577), (23, 3120), (27, 2471), (29, 3126)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0X0Y0_check. -/
theorem Z1Split23A0X0Y0_check : checkGrid m4TZ1 3 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split23A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0X0Y0_pairs. -/
theorem Z1Split23A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split23A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split23A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0X0_pairs. -/
theorem Z1Split23A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split23A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0_pairs. -/
theorem Z1Split23A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split23A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split23_check. -/
theorem Z1Split23_check : checkSplit m4TZ1 (0, 1, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split23A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split24A0X0Y0Certs : List (Nat × Nat) := [
  (15, 878), (57, 3206), (66, 3184), (68, 1586), (136, 3057),
  (142, 3031), (155, 3006), (159, 2505), (164, 2462), (255, 822),
  (264, 3180), (265, 1555), (357, 707), (362, 1590), (368, 2989),
  (369, 2527), (406, 3222), (418, 1516), (423, 2534), (429, 742)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0X0Y0_check. -/
theorem Z1Split24A0X0Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split24A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0X0Y0_pairs. -/
theorem Z1Split24A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split24A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split24A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0X0_pairs. -/
theorem Z1Split24A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split24A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0_pairs. -/
theorem Z1Split24A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split24A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split24_check. -/
theorem Z1Split24_check : checkSplit m4TZ1 (0, 2, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split24A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split25A0X0Y0Certs : List (Nat × Nat) := [
  (275, 357), (277, 358), (336, 421), (408, 476), (584, 610),
  (741, 727), (893, 841), (952, 866), (954, 868), (958, 870),
  (1099, 982), (1147, 1017), (1259, 1086), (1422, 1224), (1443, 1241),
  (1625, 1356), (1772, 1469), (1786, 1479), (1832, 1503), (1837, 1509),
  (1919, 1560), (1935, 1573), (2072, 1672), (2200, 1744), (2271, 1819),
  (2340, 1870), (2530, 1980), (2626, 2115), (2784, 2210), (2834, 2246),
  (2942, 2370), (2980, 2383), (2986, 2385), (2993, 2395), (3061, 2429),
  (3073, 2438), (3080, 2450), (3196, 2533), (3308, 2613), (3390, 2665),
  (3577, 2796), (3669, 2962), (3711, 2985), (3726, 3000), (3792, 3027),
  (3802, 3033), (3813, 3047), (3909, 3108), (3925, 3129), (4005, 3178)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0Y0_check. -/
theorem Z1Split25A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split25A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0Y0_pairs. -/
theorem Z1Split25A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split25A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z1Split25A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0_pairs. -/
theorem Z1Split25A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split25A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0_pairs. -/
theorem Z1Split25A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split25A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split25_check. -/
theorem Z1Split25_check : checkSplit m4TZ1 (0, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split25A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split26A0X0Y0Certs : List (Nat × Nat) := [
  (1, 36), (15, 103), (17, 107), (66, 324), (68, 329),
  (72, 342), (147, 722), (153, 788), (155, 790), (159, 800),
  (165, 835), (264, 1500), (270, 1544), (362, 2381), (368, 2428),
  (374, 2501), (417, 2981), (423, 3025), (429, 3106), (433, 3176)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0X0Y0_check. -/
theorem Z1Split26A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split26A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0X0Y0_pairs. -/
theorem Z1Split26A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split26A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split26A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0X0_pairs. -/
theorem Z1Split26A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split26A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0_pairs. -/
theorem Z1Split26A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split26A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split26_check. -/
theorem Z1Split26_check : checkSplit m4TZ1 (0, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split26A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split27A0X0Y0Certs : List (Nat × Nat) := [
  (0, 13), (2, 34), (6, 101), (11, 270), (12, 323),
  (17, 682), (18, 780), (23, 1448), (27, 2338), (29, 2934)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0X0Y0_check. -/
theorem Z1Split27A0X0Y0_check : checkGrid m4TZ1 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split27A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0X0Y0_pairs. -/
theorem Z1Split27A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split27A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split27A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0X0_pairs. -/
theorem Z1Split27A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split27A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0_pairs. -/
theorem Z1Split27A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split27A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split27_check. -/
theorem Z1Split27_check : checkSplit m4TZ1 (0, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split27A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split28A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0X0Y0_check. -/
theorem Z1Split28A0X0Y0_check : checkGrid m4TZ1 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split28A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0X0Y0_pairs. -/
theorem Z1Split28A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split28A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split28A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0X0_pairs. -/
theorem Z1Split28A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split28A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0_pairs. -/
theorem Z1Split28A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split28A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split28_check. -/
theorem Z1Split28_check : checkSplit m4TZ1 (0, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split28A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split29A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0X0Y0_check. -/
theorem Z1Split29A0X0Y0_check : checkGrid m4TZ1 3 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split29A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0X0Y0_pairs. -/
theorem Z1Split29A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split29A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split29A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0X0_pairs. -/
theorem Z1Split29A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split29A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0_pairs. -/
theorem Z1Split29A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split29A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split29_check. -/
theorem Z1Split29_check : checkSplit m4TZ1 (1, 0, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split29A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split30A0X0Y0Certs : List (Nat × Nat) := [
  (15, 2035), (41, 2195), (81, 2909), (90, 2616), (137, 1528),
  (181, 2615), (212, 497), (293, 2484), (349, 2025), (364, 496),
  (396, 1126), (477, 3158), (534, 2893), (549, 1122), (582, 2039),
  (659, 2879), (693, 2124), (738, 2895), (817, 493), (883, 1116)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0X0Y0_check. -/
theorem Z1Split30A0X0Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split30A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0X0Y0_pairs. -/
theorem Z1Split30A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split30A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split30A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0X0_pairs. -/
theorem Z1Split30A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split30A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0_pairs. -/
theorem Z1Split30A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split30A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split30_check. -/
theorem Z1Split30_check : checkSplit m4TZ1 (1, 1, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split30A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split31A0X0Y0Certs : List (Nat × Nat) := [
  (181, 249), (326, 2279), (884, 144), (1162, 657), (2664, 422),
  (2844, 1427), (4904, 464), (5166, 2729), (5355, 984), (5552, 2329),
  (7430, 160), (7625, 1070), (7913, 2843), (8082, 1821), (10109, 471),
  (10306, 1959), (11954, 1080), (12127, 2822), (12659, 2846), (12939, 1974)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0X0Y0_check. -/
theorem Z1Split31A0X0Y0_check : checkGrid m4TZ1 3 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split31A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0X0Y0_pairs. -/
theorem Z1Split31A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split31A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z1Split31A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0X0_pairs. -/
theorem Z1Split31A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split31A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0_pairs. -/
theorem Z1Split31A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split31A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split31_check. -/
theorem Z1Split31_check : checkSplit m4TZ1 (1, 2, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split31A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split32A0X0Y0Certs : List (Nat × Nat) := [
  (86, 391), (98, 456), (298, 1809), (335, 2132), (995, 604),
  (1055, 939), (1073, 1055), (1198, 2097), (2636, 141), (2851, 1339),
  (2906, 1754), (2929, 1938), (4826, 203), (4834, 228), (5106, 1966),
  (5177, 2648), (5308, 417), (5523, 1847), (5561, 2178), (5622, 2778),
  (7510, 562), (7524, 619), (7593, 1028), (7774, 2585), (7861, 158),
  (8017, 976), (8066, 1318), (8215, 2603), (10037, 159), (10231, 1249),
  (10251, 1373), (10319, 1895), (11845, 469), (11977, 1309), (12091, 2232),
  (12143, 2709), (12626, 77), (12820, 1076), (12923, 1862), (12944, 2099)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0X0Y0_check. -/
theorem Z1Split32A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split32A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0X0Y0_pairs. -/
theorem Z1Split32A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split32A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z1Split32A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0X0_pairs. -/
theorem Z1Split32A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split32A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0_pairs. -/
theorem Z1Split32A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split32A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split32_check. -/
theorem Z1Split32_check : checkSplit m4TZ1 (1, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split32A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split33A0X0Y0Certs : List (Nat × Nat) := [
  (15, 528), (16, 592), (81, 1161), (82, 1307), (181, 19),
  (206, 2086), (349, 884), (350, 1003), (364, 55), (365, 68),
  (534, 1629), (535, 1840), (549, 188), (550, 221), (693, 44),
  (718, 2583), (817, 118), (818, 147), (883, 364), (884, 437)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0X0Y0_check. -/
theorem Z1Split33A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split33A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0X0Y0_pairs. -/
theorem Z1Split33A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split33A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split33A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0X0_pairs. -/
theorem Z1Split33A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split33A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0_pairs. -/
theorem Z1Split33A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split33A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split33_check. -/
theorem Z1Split33_check : checkSplit m4TZ1 (1, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split33A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split34A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0X0Y0_check. -/
theorem Z1Split34A0X0Y0_check : checkGrid m4TZ1 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split34A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0X0Y0_pairs. -/
theorem Z1Split34A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split34A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split34A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0X0_pairs. -/
theorem Z1Split34A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split34A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0_pairs. -/
theorem Z1Split34A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split34A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split34_check. -/
theorem Z1Split34_check : checkSplit m4TZ1 (1, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split34A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split35A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0X0Y0_check. -/
theorem Z1Split35A0X0Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split35A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0X0Y0_pairs. -/
theorem Z1Split35A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split35A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split35A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0X0_pairs. -/
theorem Z1Split35A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split35A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0_pairs. -/
theorem Z1Split35A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split35A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split35_check. -/
theorem Z1Split35_check : checkSplit m4TZ1 (2, 0, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split35A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split36A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0X0Y0_check. -/
theorem Z1Split36A0X0Y0_check : checkGrid m4TZ1 3 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split36A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0X0Y0_pairs. -/
theorem Z1Split36A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split36A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split36A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0X0_pairs. -/
theorem Z1Split36A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split36A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0_pairs. -/
theorem Z1Split36A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split36A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split36_check. -/
theorem Z1Split36_check : checkSplit m4TZ1 (2, 1, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split36A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split37A0X0Y0Certs : List (Nat × Nat) := [
  (7832, 39), (26782, 1377), (31774, 112), (33594, 459), (50885, 3079),
  (64727, 2243), (72285, 352), (74154, 1059), (74553, 857), (99032, 1677),
  (110375, 1945), (110629, 692)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X0Y0_check. -/
theorem Z1Split37A0X0Y0_check : checkGrid m4TZ1 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X0Y0_pairs. -/
theorem Z1Split37A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split37A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X0_pairs. -/
theorem Z1Split37A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split37A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split37A0X1Y0Certs : List (Nat × Nat) := [
  (6855, 2102), (9780, 1165), (41375, 230), (42598, 2794), (43325, 1485),
  (66250, 622), (68246, 2608), (69529, 2408)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X1Y0_check. -/
theorem Z1Split37A0X1Y0_check : checkGrid m4TZ1 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X1Y0_pairs. -/
theorem Z1Split37A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split37A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X1_pairs. -/
theorem Z1Split37A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split37A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0_pairs. -/
theorem Z1Split37A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split37A0X0_pairs x hx y hy hw
  · exact Z1Split37A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split37_check. -/
theorem Z1Split37_check : checkSplit m4TZ1 (2, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split37A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split38A0X0Y0Certs : List (Nat × Nat) := [
  (54, 1626), (513, 41), (2167, 116), (4431, 1158), (4609, 887),
  (4963, 367), (8101, 14), (11224, 54), (12525, 527), (12999, 187)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0X0Y0_check. -/
theorem Z1Split38A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split38A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0X0Y0_pairs. -/
theorem Z1Split38A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split38A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split38A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0X0_pairs. -/
theorem Z1Split38A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split38A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0_pairs. -/
theorem Z1Split38A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split38A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split38_check. -/
theorem Z1Split38_check : checkSplit m4TZ1 (2, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split38A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split39A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0X0Y0_check. -/
theorem Z1Split39A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split39A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0X0Y0_pairs. -/
theorem Z1Split39A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split39A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split39A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0X0_pairs. -/
theorem Z1Split39A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split39A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0_pairs. -/
theorem Z1Split39A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split39A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split39_check. -/
theorem Z1Split39_check : checkSplit m4TZ1 (2, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split39A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split40A0X0Y0Certs : List (Nat × Nat) := [
  (250, 351), (514, 566), (897, 848), (913, 853), (987, 903),
  (990, 906), (1206, 1052), (1455, 1251), (1475, 1260), (1581, 1337),
  (1586, 1341), (1877, 1532), (2097, 1678), (2104, 1682), (2222, 1758),
  (2386, 1891), (2394, 1898), (2455, 1933), (2715, 2176), (2724, 2181),
  (2864, 2274), (3056, 2424), (3066, 2432), (3139, 2489), (3291, 2602),
  (3461, 2705), (3473, 2715), (3691, 2973), (3902, 3103), (3917, 3113)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0Y0_check. -/
theorem Z1Split40A0X0Y0_check : checkGrid m4TZ1 2 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split40A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0Y0_pairs. -/
theorem Z1Split40A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split40A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
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
      exact Z1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z1Split40A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0_pairs. -/
theorem Z1Split40A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split40A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0_pairs. -/
theorem Z1Split40A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split40A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split40_check. -/
theorem Z1Split40_check : checkSplit m4TZ1 (3, 0, 3, 2) = true := by
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
    · exact Z1Split40A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split41A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0X0Y0_check. -/
theorem Z1Split41A0X0Y0_check : checkGrid m4TZ1 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split41A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0X0Y0_pairs. -/
theorem Z1Split41A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split41A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
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
      exact Z1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z1Split41A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0X0_pairs. -/
theorem Z1Split41A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split41A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0_pairs. -/
theorem Z1Split41A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split41A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split41_check. -/
theorem Z1Split41_check : checkSplit m4TZ1 (3, 1, 2, 2) = true := by
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
    · exact Z1Split41A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split42A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0X0Y0_check. -/
theorem Z1Split42A0X0Y0_check : checkGrid m4TZ1 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split42A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0X0Y0_pairs. -/
theorem Z1Split42A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split42A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
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
      exact Z1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split42A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0X0_pairs. -/
theorem Z1Split42A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split42A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0_pairs. -/
theorem Z1Split42A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split42A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split42_check. -/
theorem Z1Split42_check : checkSplit m4TZ1 (3, 2, 1, 2) = true := by
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
    · exact Z1Split42A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split43A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X0Y0_check. -/
theorem Z1Split43A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split43A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X0Y0_pairs. -/
theorem Z1Split43A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split43A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split43A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X0_pairs. -/
theorem Z1Split43A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split43A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0_pairs. -/
theorem Z1Split43A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split43A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split43_check. -/
theorem Z1Split43_check : checkSplit m4TZ1 (3, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split43A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split44A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0X0Y0_check. -/
theorem Z1Split44A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split44A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0X0Y0_pairs. -/
theorem Z1Split44A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split44A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
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
      exact Z1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split44A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0X0_pairs. -/
theorem Z1Split44A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split44A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0_pairs. -/
theorem Z1Split44A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split44A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split44_check. -/
theorem Z1Split44_check : checkSplit m4TZ1 (4, 0, 2, 2) = true := by
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
    · exact Z1Split44A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split45A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0X0Y0_check. -/
theorem Z1Split45A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split45A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0X0Y0_pairs. -/
theorem Z1Split45A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split45A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split45A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0X0_pairs. -/
theorem Z1Split45A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split45A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0_pairs. -/
theorem Z1Split45A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split45A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split45_check. -/
theorem Z1Split45_check : checkSplit m4TZ1 (4, 1, 1, 2) = true := by
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
    · exact Z1Split45A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split46A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0X0Y0_check. -/
theorem Z1Split46A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split46A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0X0Y0_pairs. -/
theorem Z1Split46A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split46A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split46A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0X0_pairs. -/
theorem Z1Split46A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split46A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0_pairs. -/
theorem Z1Split46A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split46A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split46_check. -/
theorem Z1Split46_check : checkSplit m4TZ1 (4, 2, 0, 2) = true := by
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
    · exact Z1Split46A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split47A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0X0Y0_check. -/
theorem Z1Split47A0X0Y0_check : checkGrid m4TZ1 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split47A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0X0Y0_pairs. -/
theorem Z1Split47A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split47A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split47A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0X0_pairs. -/
theorem Z1Split47A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split47A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0_pairs. -/
theorem Z1Split47A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split47A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split47_check. -/
theorem Z1Split47_check : checkSplit m4TZ1 (5, 0, 1, 2) = true := by
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
    · exact Z1Split47A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split48A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0X0Y0_check. -/
theorem Z1Split48A0X0Y0_check : checkGrid m4TZ1 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split48A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0X0Y0_pairs. -/
theorem Z1Split48A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split48A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split48A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0X0_pairs. -/
theorem Z1Split48A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split48A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0_pairs. -/
theorem Z1Split48A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split48A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split48_check. -/
theorem Z1Split48_check : checkSplit m4TZ1 (5, 1, 0, 2) = true := by
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
    · exact Z1Split48A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split49A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0X0Y0_check. -/
theorem Z1Split49A0X0Y0_check : checkGrid m4TZ1 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split49A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0X0Y0_pairs. -/
theorem Z1Split49A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split49A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split49A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0X0_pairs. -/
theorem Z1Split49A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split49A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0_pairs. -/
theorem Z1Split49A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split49A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split49_check. -/
theorem Z1Split49_check : checkSplit m4TZ1 (6, 0, 0, 2) = true := by
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
    · exact Z1Split49A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split50A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0X0Y0_check. -/
theorem Z1Split50A0X0Y0_check : checkGrid m4TZ1 3 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split50A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0X0Y0_pairs. -/
theorem Z1Split50A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 8 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split50A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split50A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0X0_pairs. -/
theorem Z1Split50A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 8 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split50A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0_pairs. -/
theorem Z1Split50A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 8 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split50A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split50_check. -/
theorem Z1Split50_check : checkSplit m4TZ1 (0, 0, 8, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split50A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split51A0X0Y0Certs : List (Nat × Nat) := [
  (1, 2033), (3, 2021), (4, 2907), (5, 1155), (7, 2886),
  (8, 1153), (9, 2791), (10, 2079), (13, 2290), (14, 2077),
  (15, 1712), (16, 2914), (19, 1282), (20, 2888), (21, 1298),
  (22, 2748), (24, 1765), (25, 2304), (26, 2165), (28, 2660)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0X0Y0_check. -/
theorem Z1Split51A0X0Y0_check : checkGrid m4TZ1 3 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split51A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0X0Y0_pairs. -/
theorem Z1Split51A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split51A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split51A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0X0_pairs. -/
theorem Z1Split51A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split51A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0_pairs. -/
theorem Z1Split51A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split51A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split51_check. -/
theorem Z1Split51_check : checkSplit m4TZ1 (0, 1, 7, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split51A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split52A0X0Y0Certs : List (Nat × Nat) := [
  (4, 1104), (25, 2005), (33, 520), (55, 1558), (61, 1581),
  (77, 3224), (87, 2864), (101, 1154), (138, 2531), (148, 2464),
  (170, 3225), (186, 1797), (206, 2078), (253, 3226), (259, 3231),
  (271, 3062), (297, 1775), (322, 2910), (351, 845), (353, 3228),
  (363, 3209), (404, 2847), (408, 877), (412, 3232), (424, 3074)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0X0Y0_check. -/
theorem Z1Split52A0X0Y0_check : checkGrid m4TZ1 3 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split52A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0X0Y0_pairs. -/
theorem Z1Split52A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split52A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split52A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0X0_pairs. -/
theorem Z1Split52A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split52A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0_pairs. -/
theorem Z1Split52A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split52A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split52_check. -/
theorem Z1Split52_check : checkSplit m4TZ1 (0, 2, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split52A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split53A0X0Y0Certs : List (Nat × Nat) := [
  (21, 3127), (180, 2540), (221, 2539), (235, 3053), (237, 2529),
  (275, 3121), (281, 3140), (695, 3194), (748, 3220), (757, 1576),
  (817, 3199), (831, 1562), (833, 3207), (873, 3221), (882, 3230),
  (884, 728), (888, 3227), (954, 2474), (964, 2520), (1786, 3139),
  (1826, 3037), (1828, 2538), (1832, 3055), (1839, 3078), (1918, 873),
  (1924, 3214), (1930, 3193), (1941, 2441), (2926, 3117), (2980, 2536),
  (2991, 3075), (2993, 2511), (3002, 3132), (3063, 1583), (3067, 3205),
  (3072, 3223), (3073, 743), (3084, 1589), (3089, 744), (3178, 3134),
  (3189, 3073), (3195, 1517), (3671, 2444), (3715, 3077), (3720, 2526),
  (3790, 1592), (3792, 3191), (3801, 844), (3809, 1563), (3813, 3198),
  (3824, 2388), (3913, 2473), (3918, 2528), (3919, 2990), (3924, 3208),
  (3925, 1591), (4007, 2407), (4016, 3061), (4022, 1556), (4028, 2463)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0Y0_check. -/
theorem Z1Split53A0X0Y0_check : checkGrid m4TZ1 3 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split53A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0Y0_pairs. -/
theorem Z1Split53A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split53A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z1Split53A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0_pairs. -/
theorem Z1Split53A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split53A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0_pairs. -/
theorem Z1Split53A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split53A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split53_check. -/
theorem Z1Split53_check : checkSplit m4TZ1 (0, 3, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split53A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y0Certs : List (Nat × Nat) := [
  (320, 258), (351, 293), (661, 359), (1319, 514), (1758, 581),
  (2191, 653), (2363, 667), (2601, 734), (2615, 736), (2617, 737),
  (2655, 740), (2657, 741), (3240, 826), (3242, 827), (3335, 842),
  (3337, 843), (3741, 869), (3755, 871), (3757, 872), (3801, 874),
  (4009, 920), (4519, 985), (4989, 1044), (5344, 1082), (5914, 1147),
  (6134, 1208), (7220, 1296), (7363, 1328), (7956, 1386), (8495, 1418),
  (8832, 1443), (8876, 1481), (9035, 1504), (9076, 1511), (9090, 1515),
  (9130, 1519), (9136, 1520), (9590, 1554), (9596, 1557), (9601, 1561),
  (9688, 1571), (9726, 1574), (9732, 1575), (9739, 1578), (9743, 1580),
  (9748, 1582), (9809, 1587), (9813, 1588), (11003, 1690), (11238, 1719),
  (12347, 1822), (12713, 1866), (13295, 1922), (13827, 1952), (14099, 1976),
  (14879, 2067), (14969, 2107), (15288, 2155), (16668, 2261), (17057, 2283),
  (17097, 2286), (17153, 2288), (17206, 2294), (17364, 2315), (17716, 2384),
  (17730, 2386), (17732, 2387), (17785, 2398), (17787, 2399), (17825, 2404),
  (17827, 2405), (17831, 2406), (18231, 2431), (18285, 2435), (18287, 2436),
  (18291, 2437), (18296, 2439), (18298, 2440), (18381, 2452), (18383, 2453),
  (18432, 2460), (18434, 2461), (18502, 2468), (18504, 2469), (18513, 2470),
  (18514, 2472), (19336, 2508), (19378, 2510), (19382, 2512), (19387, 2515),
  (19398, 2519), (19459, 2525), (19469, 2530), (19476, 2535), (19485, 2537),
  (20553, 2618), (20879, 2656), (21849, 2732), (21915, 2735), (21996, 2739),
  (22199, 2764), (22884, 2809), (22988, 2821), (23931, 2988), (23972, 2998),
  (23986, 3001), (24028, 3004), (24448, 3028), (24488, 3032), (24499, 3034),
  (24503, 3036), (24568, 3045), (24582, 3048), (24628, 3054), (24635, 3058),
  (24639, 3060), (24705, 3070), (24709, 3071), (24714, 3072), (24715, 3076),
  (25523, 3109), (25537, 3111), (25539, 3112), (25577, 3115), (25579, 3116),
  (25599, 3119), (25658, 3123), (25660, 3124), (25664, 3125), (25670, 3128),
  (25675, 3130), (25677, 3131), (25681, 3133), (25686, 3136), (26691, 3182),
  (26731, 3187), (26744, 3190), (26753, 3192), (26812, 3196), (26818, 3197),
  (26824, 3200), (26831, 3204), (26846, 3213), (26935, 3219), (26947, 3229)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y0_check. -/
theorem Z1Split54A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y0_pairs. -/
theorem Z1Split54A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · exact Z1Split54A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0_pairs. -/
theorem Z1Split54A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split54A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0_pairs. -/
theorem Z1Split54A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split54A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split54_check. -/
theorem Z1Split54_check : checkSplit m4TZ1 (0, 4, 4, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split54A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split55A0X0Y0Certs : List (Nat × Nat) := [
  (21, 110), (42, 138), (44, 140), (46, 143), (65, 162),
  (151, 248), (166, 285), (221, 330), (235, 344), (237, 345),
  (281, 360), (326, 404), (327, 408), (329, 411), (330, 415),
  (335, 420), (375, 452), (407, 475), (414, 489), (417, 494),
  (488, 553), (658, 655), (681, 691), (695, 703), (697, 706),
  (735, 724), (737, 725), (757, 739), (817, 791), (831, 801),
  (833, 802), (871, 819), (873, 821), (882, 836), (884, 838),
  (888, 839), (964, 876), (1002, 910), (1083, 953), (1084, 958),
  (1087, 963), (1088, 972), (1098, 981), (1189, 1042), (1258, 1085),
  (1261, 1096), (1263, 1098), (1270, 1108), (1274, 1117), (1334, 1176),
  (1431, 1230), (1544, 1313), (1743, 1421), (1788, 1480), (1828, 1502),
  (1839, 1510), (1843, 1514), (1909, 1546), (1913, 1547), (1918, 1553),
  (1924, 1569), (1941, 1585), (2028, 1642), (2125, 1694), (2249, 1776),
  (2250, 1784), (2253, 1790), (2254, 1803), (2270, 1817), (2304, 1848),
  (2429, 1918), (2529, 1979), (2535, 1992), (2538, 1994), (2547, 2012),
  (2551, 2026), (2625, 2112), (2633, 2123), (2813, 2235), (2818, 2238),
  (2919, 2321), (2926, 2356), (2997, 2397), (3067, 2433), (3072, 2434),
  (3084, 2451), (3089, 2456), (3090, 2459), (3178, 2504), (3184, 2507),
  (3189, 2509), (3190, 2514), (3195, 2524), (3301, 2605), (3309, 2614),
  (3522, 2758), (3553, 2781), (3557, 2783), (3610, 2848), (3614, 2851),
  (3623, 2873), (3626, 2894), (3671, 2963), (3709, 2983), (3715, 2987),
  (3720, 2997), (3790, 3026), (3801, 3030), (3807, 3043), (3818, 3052),
  (3819, 3056), (3918, 3114), (3919, 3118), (3924, 3122), (4007, 3179),
  (4016, 3186), (4017, 3189), (4022, 3195), (4023, 3202), (4028, 3218)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0Y0_check. -/
theorem Z1Split55A0X0Y0_check : checkGrid m4TZ1 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split55A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0Y0_pairs. -/
theorem Z1Split55A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split55A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z1Split55A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0_pairs. -/
theorem Z1Split55A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split55A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0_pairs. -/
theorem Z1Split55A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split55A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split55_check. -/
theorem Z1Split55_check : checkSplit m4TZ1 (0, 5, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split55A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split56A0X0Y0Certs : List (Nat × Nat) := [
  (14, 84), (35, 176), (46, 225), (54, 254), (55, 277),
  (57, 284), (94, 447), (104, 508), (124, 602), (135, 663),
  (136, 686), (138, 689), (142, 702), (164, 817), (197, 1024),
  (209, 1139), (215, 1181), (240, 1333), (252, 1434), (255, 1468),
  (259, 1478), (265, 1508), (284, 1660), (313, 1886), (324, 2054),
  (326, 2094), (340, 2166), (357, 2369), (363, 2392), (369, 2447),
  (381, 2589), (397, 2695), (406, 2946), (418, 2995), (424, 3041)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0X0Y0_check. -/
theorem Z1Split56A0X0Y0_check : checkGrid m4TZ1 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split56A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0X0Y0_pairs. -/
theorem Z1Split56A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split56A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split56A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0X0_pairs. -/
theorem Z1Split56A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split56A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0_pairs. -/
theorem Z1Split56A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split56A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split56_check. -/
theorem Z1Split56_check : checkSplit m4TZ1 (0, 6, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split56A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split57A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0X0Y0_check. -/
theorem Z1Split57A0X0Y0_check : checkGrid m4TZ1 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split57A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0X0Y0_pairs. -/
theorem Z1Split57A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split57A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split57A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0X0_pairs. -/
theorem Z1Split57A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split57A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0_pairs. -/
theorem Z1Split57A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split57A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split57_check. -/
theorem Z1Split57_check : checkSplit m4TZ1 (0, 7, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split57A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split58A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0X0Y0_check. -/
theorem Z1Split58A0X0Y0_check : checkGrid m4TZ1 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split58A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0X0Y0_pairs. -/
theorem Z1Split58A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 8 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split58A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split58A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0X0_pairs. -/
theorem Z1Split58A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 8 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split58A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0_pairs. -/
theorem Z1Split58A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 8 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split58A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split58_check. -/
theorem Z1Split58_check : checkSplit m4TZ1 (0, 8, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split58A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split59A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0X0Y0_check. -/
theorem Z1Split59A0X0Y0_check : checkGrid m4TZ1 3 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split59A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0X0Y0_pairs. -/
theorem Z1Split59A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split59A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split59A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0X0_pairs. -/
theorem Z1Split59A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split59A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0_pairs. -/
theorem Z1Split59A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split59A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split59_check. -/
theorem Z1Split59_check : checkSplit m4TZ1 (1, 0, 7, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split59A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split60A0X0Y0Certs : List (Nat × Nat) := [
  (10, 1281), (57, 2276), (76, 1761), (102, 3246), (149, 2467),
  (202, 1955), (228, 3019), (281, 3085), (344, 1708), (386, 2817),
  (390, 1138), (467, 2019), (530, 1255), (545, 2790), (572, 2053),
  (653, 2883), (715, 1387), (726, 2928), (838, 2262), (878, 2292)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0X0Y0_check. -/
theorem Z1Split60A0X0Y0_check : checkGrid m4TZ1 3 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split60A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0X0Y0_pairs. -/
theorem Z1Split60A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split60A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split60A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0X0_pairs. -/
theorem Z1Split60A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split60A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0_pairs. -/
theorem Z1Split60A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split60A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split60_check. -/
theorem Z1Split60_check : checkSplit m4TZ1 (1, 1, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split60A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split61A0X0Y0Certs : List (Nat × Nat) := [
  (99, 1277), (106, 576), (115, 1799), (119, 1807), (180, 2825),
  (279, 517), (297, 2044), (298, 2813), (524, 1788), (573, 2143),
  (588, 2202), (605, 3168), (700, 2572), (746, 1928), (788, 3165),
  (874, 2902), (894, 1150), (1074, 1705), (1084, 1283), (1096, 1785),
  (1100, 2028), (1161, 2903), (1198, 2768), (1341, 1794), (1443, 2774),
  (1453, 2693), (1536, 1326), (1662, 2917), (1713, 2920), (1722, 3237),
  (1741, 491), (1928, 1620), (1993, 856), (1999, 761), (2109, 3065),
  (2135, 2775), (2152, 502), (2459, 3145), (2635, 2716), (2636, 2320),
  (2647, 1793), (2695, 2070), (2823, 2733), (2842, 1325), (2911, 2898),
  (2930, 1219), (3106, 3017), (3152, 1704), (3192, 760), (3304, 2411),
  (3316, 1529), (3372, 2152), (3463, 3066), (3695, 1266), (3932, 1113),
  (3992, 1134), (4176, 2476), (4214, 2546), (4268, 1131), (4278, 1613),
  (4321, 1114), (4444, 759), (4835, 1710), (4903, 2330), (4959, 938),
  (4966, 1806), (4970, 1801), (4996, 427), (5082, 2074), (5106, 2265),
  (5242, 1072), (5307, 1902), (5308, 2769), (5329, 1703), (5404, 2828),
  (5549, 2151), (5602, 2645), (5623, 956), (5675, 971), (5803, 1125),
  (5819, 1124), (5871, 1213), (5925, 1612), (6006, 2486), (6018, 3086),
  (6136, 716), (6582, 2022), (6597, 2020), (6695, 2052), (6879, 3010),
  (6890, 3148), (6937, 2049), (6949, 2564), (7157, 1611), (7399, 2878),
  (7402, 990), (7525, 1275), (7624, 2885), (7678, 1752), (7687, 2014),
  (7691, 1804), (7774, 2319), (7871, 968), (7874, 974), (7912, 1962),
  (8016, 2724), (8017, 2326), (8049, 1200), (8125, 2620), (8216, 1782),
  (8332, 850), (8341, 1802), (8401, 2037), (8536, 2038), (8639, 2567),
  (8673, 3160), (8689, 2031), (8824, 1538), (9190, 3245), (9212, 2925),
  (9277, 2890), (9300, 2884), (9388, 2924), (9548, 961), (9561, 1293),
  (9883, 2566), (10030, 2186), (10037, 2767), (10045, 1827), (10086, 1781),
  (10239, 2876), (10252, 1685), (10282, 2282), (10308, 1860), (10495, 2905),
  (10501, 2900), (10597, 964), (10609, 1715), (10695, 2912), (10791, 2913),
  (10873, 3249), (11115, 2497), (11707, 3248), (11754, 658), (11832, 1371),
  (11845, 2318), (11859, 2269), (11923, 1274), (12077, 2153), (12092, 965),
  (12130, 2644), (12520, 3172), (12658, 1428), (12698, 973), (12701, 970),
  (12801, 2231), (12820, 2763), (12840, 2117), (12904, 1683), (12945, 1795)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0X0Y0_check. -/
theorem Z1Split61A0X0Y0_check : checkGrid m4TZ1 3 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split61A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0X0Y0_pairs. -/
theorem Z1Split61A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split61A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z1Split61A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0X0_pairs. -/
theorem Z1Split61A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split61A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0_pairs. -/
theorem Z1Split61A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split61A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split61_check. -/
theorem Z1Split61_check : checkSplit m4TZ1 (1, 2, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split61A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split62A0X0Y0Certs : List (Nat × Nat) := [
  (67, 1658), (1006, 2643), (1051, 2766), (1068, 498), (1275, 1786),
  (1327, 979), (1449, 1656), (1766, 2241), (2244, 1749), (2721, 2810),
  (3479, 1907), (7672, 2687), (7731, 2273), (8533, 423), (8684, 1720),
  (9641, 412), (9674, 2747), (10253, 937), (10324, 2306), (10348, 1127),
  (10599, 2736), (10672, 1437), (10718, 1816), (10952, 629), (14121, 2617),
  (15781, 2114), (16521, 2410), (16953, 1521), (22585, 1831), (25629, 986),
  (25729, 1751), (25925, 1415), (26492, 2671), (26667, 966), (26853, 2042),
  (26974, 1384), (27014, 2161), (27926, 1242), (27962, 2113), (27964, 2226),
  (28488, 410), (31598, 505), (33830, 2490), (37504, 3084), (38412, 2477),
  (43619, 2466), (44729, 1194), (45158, 2317), (45165, 518), (45196, 2130),
  (45935, 1079), (45987, 1808), (46865, 1189), (46908, 1248), (47256, 2787),
  (47389, 1405), (48129, 2263), (48790, 409), (48802, 1995), (48881, 2259),
  (49197, 1763), (49390, 1087), (49891, 1227), (50074, 1292), (51266, 1823),
  (51407, 2310), (52036, 1796), (52303, 2874), (53195, 962), (56787, 1137),
  (57106, 3003), (62824, 2018), (64031, 3149), (68811, 3083), (69436, 472),
  (70164, 1291), (70468, 2755), (70480, 1151), (70528, 561), (70670, 2289),
  (71167, 405), (71355, 2302), (71572, 1973), (71618, 2058), (72599, 1068),
  (73388, 1924), (73498, 959), (73532, 2852), (73579, 1742), (73755, 2256),
  (74159, 2704), (74492, 1969), (74840, 1981), (75478, 1035), (76442, 2125),
  (76702, 2287), (78412, 1789), (80855, 2027), (82140, 861), (88186, 2882),
  (89236, 1884), (91709, 1894), (94653, 1081), (94882, 2209), (94944, 954),
  (95041, 2075), (95483, 1247), (95705, 1913), (96200, 1745), (96691, 1957),
  (96760, 2646), (96982, 2722), (96984, 2606), (98197, 2896), (99989, 1314),
  (103076, 1394), (109024, 2708), (109690, 1996), (109702, 416), (110070, 2819),
  (110191, 1675), (110598, 1285), (110939, 983), (111651, 1721), (112170, 1975),
  (112305, 1779), (112455, 2897), (112983, 2750), (116387, 2275), (117833, 1420),
  (118158, 2853), (118192, 975), (118792, 1237), (118822, 2175), (119065, 2815),
  (119329, 644), (119807, 1811), (120330, 1820), (120381, 2621), (121365, 2734)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0Y0_check. -/
theorem Z1Split62A0X0Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split62A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0Y0_pairs. -/
theorem Z1Split62A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split62A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact Z1Split62A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0_pairs. -/
theorem Z1Split62A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split62A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0_pairs. -/
theorem Z1Split62A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split62A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split62_check. -/
theorem Z1Split62_check : checkSplit m4TZ1 (1, 3, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split62A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split63A0X0Y0Certs : List (Nat × Nat) := [
  (119, 215), (146, 244), (451, 515), (654, 652), (1000, 909),
  (1252, 1077), (1588, 1343), (1644, 1370), (1765, 1441), (2152, 1717),
  (2545, 2007), (2696, 2160), (2779, 2206), (2794, 2218), (3358, 2642),
  (3508, 2743), (3596, 2818), (4775, 712), (8679, 584), (8768, 646),
  (9133, 917), (9310, 1043), (9446, 1148), (9754, 1364), (9857, 1414),
  (10240, 1689), (10242, 1691), (10461, 1872), (10643, 1971), (10752, 2122),
  (10847, 2183), (10929, 2230), (10931, 2234), (11704, 2801), (11741, 2867),
  (12198, 87), (18115, 1531), (22468, 1727), (24377, 86), (24765, 473),
  (25548, 1041), (25581, 1057), (25899, 1300), (25983, 1355), (26087, 1407),
  (26503, 1711), (26693, 1868), (26790, 1919), (26941, 2059), (26957, 2068),
  (27157, 2219), (27273, 2309), (27735, 2654), (27751, 2667), (27808, 2696),
  (28582, 257), (33822, 1182), (39674, 2488), (42465, 1525), (44960, 381),
  (45000, 425), (45056, 463), (45126, 543), (45753, 977), (45846, 1040),
  (46185, 1289), (47014, 1881), (47052, 1897), (47201, 1999), (47255, 2066),
  (47303, 2131), (47507, 2258), (47563, 2300), (47989, 2632), (48046, 2662),
  (48063, 2677), (48880, 256), (49959, 1067), (49975, 1083), (50178, 1253),
  (50243, 1288), (50776, 1662), (51103, 1889), (51147, 1915), (51198, 1940),
  (51297, 2057), (51501, 2208), (51618, 2293), (52000, 2591), (52044, 2631),
  (52097, 2658), (52172, 2697), (52243, 2759), (53457, 666), (56976, 239),
  (64878, 3162), (68082, 2481), (69558, 575), (69679, 656), (70043, 921),
  (70124, 988), (70260, 1069), (70399, 1204), (70403, 1207), (70646, 1358),
  (71284, 1814), (71366, 1877), (71444, 1912), (71856, 2248), (72322, 2607),
  (72431, 2681), (72490, 2712), (72575, 2782), (72637, 2857), (73161, 181),
  (73483, 470), (73675, 618), (73754, 665), (74348, 1105), (74712, 1363),
  (75157, 1676), (75229, 1716), (75402, 1859), (75584, 1956), (75606, 1977),
  (75693, 2106), (75919, 2250), (76365, 2594), (76537, 2701), (76600, 2754),
  (76645, 2786), (78908, 1442), (81830, 639), (88594, 2636), (93287, 3155),
  (93460, 180), (93719, 424), (93977, 621), (94032, 651), (94891, 1278),
  (94953, 1332), (95124, 1422), (95138, 1440), (95539, 1722), (95656, 1825),
  (95724, 1874), (95885, 1958), (96030, 2136), (96088, 2169), (96165, 2212),
  (96780, 2674), (96896, 2749), (100040, 2095), (103202, 1399), (109018, 2702),
  (110069, 513), (110230, 628), (110723, 987), (110976, 1191), (111204, 1338),
  (111269, 1375), (111354, 1412), (111373, 1436), (111765, 1714), (111839, 1756),
  (112224, 2098), (112312, 2158), (112321, 2163), (112333, 2172), (112540, 2322),
  (113015, 2670), (113217, 2820), (116385, 2168), (117789, 145), (118072, 418),
  (118894, 1021), (119005, 1100), (119064, 1146), (119166, 1228), (119268, 1290),
  (119289, 1317), (119410, 1383), (120015, 1824), (120088, 1878), (120362, 2111),
  (120459, 2177), (120559, 2240), (120649, 2305), (121045, 2610), (121321, 2799)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0Y0_check. -/
theorem Z1Split63A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split63A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0Y0_pairs. -/
theorem Z1Split63A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split63A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact Z1Split63A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0_pairs. -/
theorem Z1Split63A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split63A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0_pairs. -/
theorem Z1Split63A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split63A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split63_check. -/
theorem Z1Split63_check : checkSplit m4TZ1 (1, 4, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split63A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split64A0X0Y0Certs : List (Nat × Nat) := [
  (85, 387), (180, 914), (181, 918), (204, 1060), (239, 1330),
  (297, 1768), (326, 2092), (387, 2625), (874, 52), (884, 85),
  (983, 550), (1054, 931), (1161, 1700), (1162, 1713), (1190, 1944),
  (1209, 2157), (2635, 135), (2664, 253), (2805, 1020), (2823, 1174),
  (2834, 1223), (2844, 1312), (2905, 1737), (3013, 2795), (4825, 199),
  (4903, 572), (4904, 578), (4915, 623), (5082, 1767), (5090, 1854),
  (5123, 2148), (5166, 2587), (5242, 124), (5307, 397), (5355, 662),
  (5411, 1011), (5499, 1640), (5530, 1876), (5552, 2110), (5606, 2609),
  (7399, 51), (7430, 177), (7509, 555), (7571, 901), (7624, 1271),
  (7625, 1287), (7642, 1376), (7783, 2628), (7854, 132), (7912, 377),
  (7913, 380), (7929, 460), (8016, 945), (8082, 1432), (8134, 1851),
  (8224, 2673), (10030, 136), (10109, 506), (10133, 613), (10230, 1235),
  (10282, 1634), (10291, 1671), (10306, 1844), (10352, 2244), (11754, 65),
  (11832, 398), (11868, 600), (11954, 1140), (11956, 1169), (11990, 1362),
  (12075, 2101), (12127, 2592), (12622, 61), (12658, 207), (12659, 211),
  (12665, 231), (12801, 946), (12853, 1322), (12939, 2055), (12960, 2217)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0X0Y0_check. -/
theorem Z1Split64A0X0Y0_check : checkGrid m4TZ1 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0X0Y0_pairs. -/
theorem Z1Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split64A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z1Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0X0_pairs. -/
theorem Z1Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0_pairs. -/
theorem Z1Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split64_check. -/
theorem Z1Split64_check : checkSplit m4TZ1 (1, 5, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split65A0X0Y0Certs : List (Nat × Nat) := [
  (47, 676), (92, 31), (143, 1452), (216, 91), (297, 2340),
  (402, 316), (479, 2938), (588, 781), (641, 273), (720, 7)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0X0Y0_check. -/
theorem Z1Split65A0X0Y0_check : checkGrid m4TZ1 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0X0Y0_pairs. -/
theorem Z1Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split65A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0X0_pairs. -/
theorem Z1Split65A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0_pairs. -/
theorem Z1Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split65_check. -/
theorem Z1Split65_check : checkSplit m4TZ1 (1, 6, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0X0Y0_check. -/
theorem Z1Split66A0X0Y0_check : checkGrid m4TZ1 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0X0Y0_pairs. -/
theorem Z1Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split66A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0X0_pairs. -/
theorem Z1Split66A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0_pairs. -/
theorem Z1Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split66_check. -/
theorem Z1Split66_check : checkSplit m4TZ1 (1, 7, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split67A0X0Y0Certs : List (Nat × Nat) := [
  (4, 2889), (25, 2443), (33, 3064), (55, 1805), (87, 3138),
  (101, 960), (138, 2011), (186, 2485), (206, 1787), (259, 2870),
  (297, 3159), (322, 1600), (363, 2006), (404, 2553), (424, 2865)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0X0Y0_check. -/
theorem Z1Split67A0X0Y0_check : checkGrid m4TZ1 3 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0X0Y0_pairs. -/
theorem Z1Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split67A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0X0_pairs. -/
theorem Z1Split67A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0_pairs. -/
theorem Z1Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split67_check. -/
theorem Z1Split67_check : checkSplit m4TZ1 (2, 0, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split67A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split68A0X0Y0Certs : List (Nat × Nat) := [
  (54, 2887), (126, 2927), (138, 2862), (143, 3243), (149, 3244),
  (272, 2659), (478, 1657), (513, 2313), (677, 2164), (750, 174),
  (761, 1559), (762, 3185), (777, 846), (1296, 1121), (1393, 2517),
  (1659, 2727), (1663, 2228), (1730, 245), (2000, 1800), (2048, 414),
  (2167, 2720), (2483, 1132), (2612, 504), (2627, 2532), (2628, 3018),
  (2639, 879), (2829, 2409), (3552, 2034), (3739, 3211), (3779, 1210),
  (4096, 468), (4155, 2073), (4159, 2043), (4285, 647), (4431, 2904),
  (4609, 2824), (4675, 1791), (4784, 969), (4930, 2731), (4963, 1961),
  (5427, 2050), (5580, 1133), (5586, 1136), (5591, 1609), (5603, 3233),
  (5925, 3081), (5958, 1655), (6401, 3173), (6457, 1549), (6888, 2908),
  (7103, 2555), (7224, 3098), (7241, 752), (7672, 1075), (7791, 2872),
  (7794, 2892), (7946, 1190), (7978, 1408), (8101, 2753), (8310, 2814),
  (8524, 1486), (8759, 2926), (8912, 2051), (8922, 2024), (8927, 2563),
  (8937, 3234), (9246, 1783), (9411, 1753), (9420, 407), (10077, 3147),
  (10203, 1261), (10247, 1602), (10736, 1965), (10876, 1798), (10891, 1033),
  (10893, 616), (11045, 413), (11078, 2295), (11224, 2190), (11772, 1286),
  (11911, 1726), (11942, 957), (12194, 2281), (12525, 2332), (12545, 2829),
  (12712, 1777), (12724, 1905), (12727, 1368), (12880, 967), (12999, 1430)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0X0Y0_check. -/
theorem Z1Split68A0X0Y0_check : checkGrid m4TZ1 3 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0X0Y0_pairs. -/
theorem Z1Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split68A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0X0_pairs. -/
theorem Z1Split68A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0_pairs. -/
theorem Z1Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split68_check. -/
theorem Z1Split68_check : checkSplit m4TZ1 (2, 1, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split68A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split69A0X0Y0Certs : List (Nat × Nat) := [
  (470, 1755), (665, 1696), (682, 2804), (731, 1193), (1795, 2860),
  (6705, 395), (6866, 1917), (6927, 1111), (7016, 2859), (7499, 1871),
  (7696, 1119), (7698, 458), (7742, 2678), (7897, 3183), (11013, 1490),
  (20050, 2565), (20099, 305), (23969, 2668), (24008, 2213), (24111, 1152),
  (24131, 1997), (24177, 2793), (24249, 2327), (25046, 2752), (25105, 2788),
  (25174, 2328), (26876, 2069), (26934, 465), (28732, 2072), (28835, 2009),
  (28913, 2207), (29611, 2016), (29816, 2757), (29871, 944), (30590, 1487),
  (31288, 2986), (31529, 2666), (31650, 1388), (31702, 2030), (31705, 1058),
  (31912, 3005), (33628, 2331), (33693, 426), (38104, 2416), (40926, 749),
  (40975, 2496), (46041, 3087), (50648, 925), (52299, 1565), (54054, 3247),
  (54128, 766), (54802, 1123), (59405, 2242), (59476, 2312), (59488, 2792),
  (60149, 1256), (60211, 1759), (60327, 2076), (60352, 2854), (60356, 2221),
  (60411, 2676), (61802, 2714), (62120, 2188), (62164, 1693), (63959, 1252),
  (64171, 1647), (64237, 1231), (64265, 2255), (64409, 1071), (64616, 2797),
  (66674, 2700), (66685, 2324), (66740, 2789), (66936, 1280), (67507, 2845),
  (67666, 2868), (67744, 1695), (69263, 2880), (69378, 1766), (69500, 2227),
  (70732, 2412), (71291, 729), (71468, 2257), (71540, 2264), (71638, 1942),
  (71819, 2901), (71825, 2266), (71861, 1941), (72099, 1246), (72246, 875),
  (74200, 2891), (74264, 989), (74492, 1564), (79353, 1157), (81273, 3091),
  (85802, 1597), (85879, 3171), (86424, 1109), (87485, 1594), (92647, 2041),
  (93532, 1610), (93938, 2956), (99044, 1730), (101559, 2542), (102922, 2916),
  (104625, 2992), (104699, 1619), (104891, 2036), (110404, 250), (110453, 1826),
  (110844, 1579), (110951, 2185), (111270, 1206), (111325, 2718)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X0Y0_check. -/
theorem Z1Split69A0X0Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X0Y0_pairs. -/
theorem Z1Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X0_pairs. -/
theorem Z1Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split69A0X1Y0Certs : List (Nat × Nat) := [
  (3, 2840), (1309, 2839), (1319, 1900), (1340, 1345), (1535, 1423),
  (1597, 1920), (1709, 1107), (3598, 214), (3826, 1118), (3878, 1417),
  (4015, 1880), (4154, 1066), (4298, 1424), (6144, 1357), (6322, 243),
  (6324, 1110), (6493, 2224), (6620, 1960), (6860, 2619), (9786, 2541),
  (12204, 1537), (12337, 830), (16389, 2071), (18259, 2002), (22704, 2145),
  (25011, 2550), (25090, 824), (25233, 2013), (26665, 2547), (32945, 3203),
  (34731, 3016), (36751, 758), (36894, 2492), (37115, 2911), (41450, 516),
  (41524, 2823), (42208, 659), (42503, 2247), (43478, 2454), (44023, 1366),
  (44240, 627), (44268, 1921), (44393, 183), (45152, 829), (46119, 2040),
  (46239, 2664), (46308, 2001), (46570, 182), (46578, 2010), (46599, 2719),
  (46649, 2189), (46779, 2760), (46846, 2323), (48731, 2029), (48949, 583),
  (49028, 2314), (49208, 2325), (49360, 2680), (49494, 1954), (51465, 2211),
  (51659, 645), (51662, 2015), (51716, 1953), (59343, 855), (61402, 3146),
  (61614, 715), (61793, 2875), (63322, 3059), (65384, 2811), (65445, 2816),
  (65571, 1426), (66361, 1149), (66435, 2871), (67912, 1429), (68252, 2116),
  (69254, 3009), (70150, 2291), (70216, 2173), (70239, 2761), (70361, 1707),
  (70566, 2762), (70657, 2223), (70858, 1382), (70989, 522), (71670, 746),
  (72688, 2842), (72891, 1232), (72959, 2858), (73167, 519), (73181, 2869),
  (73215, 1943), (73289, 1425), (73412, 2254), (73462, 2803), (75304, 2899),
  (75532, 1299), (75647, 2723), (77036, 1406), (77078, 2877), (77094, 2812),
  (77247, 1748)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X1Y0_check. -/
theorem Z1Split69A0X1Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X1Y0_pairs. -/
theorem Z1Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X1_pairs. -/
theorem Z1Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0_pairs. -/
theorem Z1Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split69A0X0_pairs x hx y hy hw
  · exact Z1Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split69_check. -/
theorem Z1Split69_check : checkSplit m4TZ1 (2, 2, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split69A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y0Certs : List (Nat × Nat) := [
  (971, 538), (11136, 455), (12866, 171), (12868, 172), (12998, 300),
  (25874, 353), (28324, 260), (28607, 511), (28664, 564), (31631, 466),
  (31884, 240), (34111, 394), (34170, 453), (34269, 547), (35652, 402),
  (37187, 401), (39558, 234), (44955, 487), (44959, 492), (54716, 509),
  (73205, 563), (76186, 486), (78469, 233), (85193, 303), (85195, 304),
  (112205, 178), (116437, 308), (129670, 235), (130231, 294)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y0_check. -/
theorem Z1Split70A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y0_pairs. -/
theorem Z1Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y1Certs : List (Nat × Nat) := [
  (612, 630), (8174, 915), (9657, 867), (11858, 617), (13001, 711),
  (34896, 615), (37603, 726), (44813, 757), (48517, 849), (63495, 567),
  (66999, 862), (70823, 669), (75725, 895), (76412, 640), (87142, 631),
  (87572, 568), (87827, 764), (87831, 765), (88884, 793), (89310, 718),
  (130343, 769), (130355, 792)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y1_check. -/
theorem Z1Split70A0X0Y1_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y1_pairs. -/
theorem Z1Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y2Certs : List (Nat × Nat) := [
  (8844, 1025), (9035, 1188), (9340, 1018), (9615, 1225), (28203, 941),
  (29531, 1199), (31571, 1195), (37508, 1022), (39653, 1078), (41152, 1053),
  (59409, 929), (59475, 993), (70953, 1144), (71091, 1254), (73366, 1031),
  (75475, 1065), (75616, 1203), (75924, 1030), (75996, 1073), (76181, 1229),
  (79406, 943), (79530, 1046), (79748, 1217), (81649, 1101), (81753, 1198),
  (81976, 951), (84534, 950), (87200, 1037), (88019, 1265), (95474, 1102),
  (95480, 1115), (100887, 934), (103021, 997), (109861, 1142), (116229, 924),
  (119659, 1209), (123337, 1262), (130599, 940)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y2_check. -/
theorem Z1Split70A0X0Y2_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y2_pairs. -/
theorem Z1Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y3Certs : List (Nat × Nat) := [
  (3406, 1526), (4456, 1536), (7717, 1331), (8841, 1385), (8903, 1413),
  (9451, 1464), (30496, 1497), (31417, 1404), (36657, 1512), (37617, 1473),
  (39555, 1381), (43115, 1369), (44880, 1527), (48268, 1393), (59800, 1593),
  (59816, 1604), (70858, 1416), (72110, 1607), (75806, 1327), (78393, 1344),
  (81512, 1367), (85372, 1552), (95673, 1608), (116800, 1349), (123189, 1518),
  (126678, 1435), (129675, 1390)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y3_check. -/
theorem Z1Split70A0X0Y3_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y3_pairs. -/
theorem Z1Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y4Certs : List (Nat × Nat) := [
  (582, 1688), (7862, 1764), (8067, 1925), (23861, 1883), (31693, 1964),
  (34285, 2000), (34901, 1702), (35302, 1991), (37201, 1890), (37670, 1873),
  (39920, 2004), (40134, 1773), (69694, 1684), (70835, 1760), (71033, 1914),
  (78491, 1746), (78531, 1772), (79827, 1968), (85314, 1885), (87252, 1812),
  (87516, 1972), (91045, 1935), (116365, 1735), (116459, 1830), (129545, 1663),
  (129907, 1909), (130170, 1728)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y4_check. -/
theorem Z1Split70A0X0Y4_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y4_pairs. -/
theorem Z1Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y5Certs : List (Nat × Nat) := [
  (186, 2196), (686, 2187), (9648, 2394), (18972, 2062), (28400, 2222),
  (28862, 2198), (29525, 2299), (31395, 2180), (34037, 2225), (34957, 2162),
  (37154, 2260), (37214, 2307), (37749, 2363), (39651, 2215), (39716, 2267),
  (51157, 2417), (74739, 2425), (76108, 2285), (79942, 2121), (81477, 2120),
  (84000, 2064), (84801, 2280), (85395, 2378), (87091, 2104), (87324, 2253),
  (93944, 2229), (101159, 2272), (110452, 2362), (129624, 2135), (129752, 2205),
  (130482, 2396), (130635, 2126)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y5_check. -/
theorem Z1Split70A0X0Y5_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y5_pairs. -/
theorem Z1Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y6Certs : List (Nat × Nat) := [
  (1787, 2630), (7930, 2629), (9223, 2449), (19513, 2482), (21598, 2495),
  (28498, 2679), (29993, 2650), (31528, 2649), (31549, 2663), (32918, 2552),
  (35272, 2770), (39723, 2652), (41577, 2499), (56168, 2690), (59416, 2475),
  (63834, 2686), (70070, 2745), (72922, 2598), (75668, 2717), (79196, 2688),
  (83471, 2455), (84350, 2698), (84809, 2675), (84868, 2703), (85313, 2669),
  (87673, 2523), (87918, 2692), (95291, 2483), (116353, 2543), (116359, 2545),
  (129931, 2711)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y6_check. -/
theorem Z1Split70A0X0Y6_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y6_pairs. -/
theorem Z1Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y7Certs : List (Nat × Nat) := [
  (1921, 2838), (1932, 2849), (1939, 2861), (2378, 3242), (8694, 2984),
  (22006, 2974), (34824, 2955), (34975, 3046), (53226, 3156), (55567, 3144),
  (55624, 3169), (56103, 3170), (57295, 3020), (70464, 2827), (71950, 2951),
  (73813, 2856), (75708, 2844), (79128, 2975), (80956, 2863), (81577, 3021),
  (85124, 3163), (97383, 3092), (102600, 3082), (105675, 2805), (108400, 3142),
  (120979, 2952), (121043, 2999)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y7_check. -/
theorem Z1Split70A0X0Y7_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y7_pairs. -/
theorem Z1Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0_pairs. -/
theorem Z1Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split70A0X0Y0_pairs x hx y hy hw
  · exact Z1Split70A0X0Y1_pairs x hx y hy hw
  · exact Z1Split70A0X0Y2_pairs x hx y hy hw
  · exact Z1Split70A0X0Y3_pairs x hx y hy hw
  · exact Z1Split70A0X0Y4_pairs x hx y hy hw
  · exact Z1Split70A0X0Y5_pairs x hx y hy hw
  · exact Z1Split70A0X0Y6_pairs x hx y hy hw
  · exact Z1Split70A0X0Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y0Certs : List (Nat × Nat) := [
  (4772, 259), (9406, 296), (11628, 445), (11747, 552), (13353, 137),
  (14580, 348), (17075, 288), (37922, 113), (49039, 467), (50076, 488),
  (50724, 128), (50880, 298), (52159, 510), (54389, 213), (54427, 251),
  (60741, 403), (81711, 385), (81749, 430), (82825, 462), (86111, 204),
  (86333, 392)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y0_check. -/
theorem Z1Split70A0X1Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y0_pairs. -/
theorem Z1Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y1Certs : List (Nat × Nat) := [
  (4120, 573), (7223, 603), (14771, 860), (38584, 704), (49407, 750),
  (49738, 612), (49766, 632), (50929, 738), (51054, 828), (54738, 898),
  (58023, 668), (77955, 643), (79968, 626), (81654, 745), (81666, 754),
  (85548, 582), (85656, 660)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y1_check. -/
theorem Z1Split70A0X1Y1_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y1_pairs. -/
theorem Z1Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y2Certs : List (Nat × Nat) := [
  (5038, 1250), (7888, 1062), (7920, 1099), (11647, 1214), (11740, 1267),
  (48710, 978), (57486, 1027), (57828, 1273), (78044, 1074), (80115, 1103),
  (82848, 1238), (83241, 1143), (88820, 1106), (90681, 952)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y2_check. -/
theorem Z1Split70A0X1Y2_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y2_pairs. -/
theorem Z1Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y3Certs : List (Nat × Nat) := [
  (1646, 1374), (1770, 1444), (4096, 1297), (4309, 1431), (7697, 1320),
  (8365, 1401), (11715, 1617), (11721, 1618), (14194, 1540), (43454, 1616),
  (51046, 1535), (51167, 1624), (57897, 1335), (60460, 1336), (66830, 1491),
  (72698, 1650), (74480, 1472), (77034, 1445), (79269, 1599), (79964, 1360),
  (80011, 1389), (81809, 1584), (86116, 1365), (87619, 1350)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y3_check. -/
theorem Z1Split70A0X1Y3_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y3_pairs. -/
theorem Z1Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y4Certs : List (Nat × Nat) := [
  (1962, 1939), (4381, 1867), (5475, 1903), (7169, 1654), (7548, 1916),
  (7619, 1951), (8032, 1901), (8141, 1963), (19718, 1855), (21487, 2003),
  (21493, 2023), (29333, 1741), (31344, 1725), (49086, 1948), (49132, 1998),
  (49690, 1674), (49948, 1865), (51885, 1757), (54769, 2008), (57828, 1990),
  (78041, 1815), (78294, 1970), (80153, 1864), (82631, 1774), (82780, 1899),
  (83277, 1888), (85523, 1667), (85719, 1813), (86321, 1879), (88631, 1681),
  (88916, 1893), (89368, 1863)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y4_check. -/
theorem Z1Split70A0X1Y4_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y4_pairs. -/
theorem Z1Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y5Certs : List (Nat × Nat) := [
  (1568, 2063), (1890, 2311), (4230, 2159), (7808, 2154), (29569, 2371),
  (32795, 2061), (46634, 2096), (48732, 2137), (49956, 2268), (53128, 2374),
  (54952, 2184), (55038, 2237), (55125, 2298), (57708, 2333), (59743, 2308),
  (61199, 2245), (76949, 2170), (78388, 2105), (79923, 2103), (86091, 2127),
  (90778, 2174), (90862, 2220)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y5_check. -/
theorem Z1Split70A0X1Y5_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y5_pairs. -/
theorem Z1Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y6Certs : List (Nat × Nat) := [
  (1981, 2751), (3235, 2560), (7915, 2611), (16819, 2742), (21167, 2562),
  (43028, 2465), (49049, 2721), (50098, 2738), (54663, 2707), (55183, 2713),
  (55222, 2744), (55271, 2784), (57649, 2657), (58780, 2725), (60865, 2756),
  (75607, 2684), (77657, 2685), (78059, 2612), (80176, 2655), (81499, 2494),
  (81605, 2574), (86234, 2599), (88793, 2597), (91046, 2730)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y6_check. -/
theorem Z1Split70A0X1Y6_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y6_pairs. -/
theorem Z1Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y7Certs : List (Nat × Nat) := [
  (6033, 3104), (10914, 3217), (19908, 3157), (45236, 2826), (47354, 3050),
  (52824, 3240), (56175, 2808), (67262, 3002), (72353, 2802), (72384, 2855),
  (78224, 3011), (79529, 2866), (82369, 2841)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y7_check. -/
theorem Z1Split70A0X1Y7_check : checkGrid m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y7_pairs. -/
theorem Z1Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1_pairs. -/
theorem Z1Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split70A0X1Y0_pairs x hx y hy hw
  · exact Z1Split70A0X1Y1_pairs x hx y hy hw
  · exact Z1Split70A0X1Y2_pairs x hx y hy hw
  · exact Z1Split70A0X1Y3_pairs x hx y hy hw
  · exact Z1Split70A0X1Y4_pairs x hx y hy hw
  · exact Z1Split70A0X1Y5_pairs x hx y hy hw
  · exact Z1Split70A0X1Y6_pairs x hx y hy hw
  · exact Z1Split70A0X1Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0_pairs. -/
theorem Z1Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split70A0X0_pairs x hx y hy hw
  · exact Z1Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split70_check. -/
theorem Z1Split70_check : checkSplit m4TZ1 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split71A0X0Y0Certs : List (Nat × Nat) := [
  (483, 227), (536, 483), (633, 1029), (681, 1372), (2144, 2834),
  (2872, 1493), (6804, 1638), (7522, 609), (7601, 1095), (7709, 1896),
  (7741, 2233), (7846, 104), (10908, 170), (11376, 325), (14282, 2382),
  (16896, 2419), (20441, 3152), (24026, 481), (25199, 2833), (26764, 1270),
  (26934, 2728), (27054, 383), (28894, 933), (29604, 130), (31025, 695),
  (31331, 78), (31564, 1354), (31642, 1983), (31718, 2710), (31825, 335),
  (33577, 376), (33628, 641), (37946, 484), (38435, 789), (41139, 1397),
  (43923, 3024), (48712, 3094), (50642, 922), (52566, 2420), (54329, 2633),
  (59564, 2836), (60236, 1093), (61803, 169), (64037, 444), (64046, 482),
  (64070, 605), (64264, 1937), (64409, 155), (64657, 1636), (64998, 927),
  (66588, 167), (66684, 620), (66836, 1646), (66947, 2647), (67130, 694),
  (67720, 1739), (69250, 388), (71167, 1494), (71662, 1988), (71824, 229),
  (72083, 1861), (72119, 2204), (72179, 2831), (72372, 810), (74130, 913),
  (74200, 1402), (74490, 531), (81116, 1089), (81360, 102), (86020, 2090),
  (87618, 928), (89439, 1499), (93896, 2480), (96626, 280), (99038, 1724),
  (101782, 3095), (104544, 708), (110346, 1698), (110404, 2278), (110746, 1471),
  (110958, 168)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X0Y0_check. -/
theorem Z1Split71A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X0Y0_pairs. -/
theorem Z1Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X0_pairs. -/
theorem Z1Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split71A0X1Y0Certs : List (Nat × Nat) := [
  (1627, 1989), (3691, 1166), (4016, 478), (6284, 1016), (6296, 1094),
  (6331, 1340), (6492, 2779), (6534, 67), (6620, 448), (7254, 1732),
  (9782, 1170), (12312, 638), (18157, 1985), (18338, 328), (24807, 80),
  (26829, 1731), (28643, 2427), (31479, 799), (32681, 278), (36807, 1524),
  (41368, 206), (41524, 1034), (42208, 82), (42408, 1175), (43423, 2372),
  (44036, 480), (44828, 127), (46224, 557), (46949, 2837), (48727, 60),
  (49361, 1090), (51361, 157), (51639, 1869), (51652, 1982), (51671, 2179),
  (51768, 48), (53934, 3107), (61386, 238), (63078, 47), (65572, 1986),
  (66238, 571), (66435, 1906), (66578, 126), (67882, 123), (67912, 241),
  (69584, 3007), (70068, 166), (70238, 1056), (70253, 1192), (70370, 2133),
  (70676, 1092), (71424, 384), (72870, 1236), (73113, 163), (75295, 200),
  (77093, 457), (77231, 1319), (77388, 2661), (77399, 2830)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X1Y0_check. -/
theorem Z1Split71A0X1Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X1Y0_pairs. -/
theorem Z1Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X1_pairs. -/
theorem Z1Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0_pairs. -/
theorem Z1Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split71A0X0_pairs x hx y hy hw
  · exact Z1Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split71_check. -/
theorem Z1Split71_check : checkSplit m4TZ1 (2, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split72A0X0Y0Certs : List (Nat × Nat) := [
  (460, 219), (791, 271), (803, 1457), (960, 8), (966, 97),
  (1512, 314), (1723, 368), (1735, 1839), (1854, 1631), (1855, 1836),
  (2006, 2088), (2056, 586), (2319, 184), (2320, 216), (2657, 679),
  (2667, 2347), (2997, 2344), (3002, 29), (3012, 317), (3918, 778),
  (4089, 190), (4102, 1306), (4279, 883), (4288, 2578), (4443, 46),
  (4468, 2581), (4655, 73), (4792, 1304), (4924, 57), (4936, 589),
  (5115, 524), (5116, 585), (5633, 1450), (5639, 2931), (6149, 2939),
  (6156, 100), (6168, 777), (7410, 11), (7611, 1163), (7612, 1302),
  (7665, 523), (7676, 2084), (7934, 435), (7958, 148), (7974, 1632),
  (8137, 120), (8138, 154), (8951, 264), (8967, 2342), (9611, 267),
  (9630, 10), (9642, 315), (9857, 674), (9869, 2940), (9906, 89),
  (10412, 30), (10543, 363), (10544, 436), (10591, 20), (10616, 2085),
  (10715, 71), (10731, 1162), (10888, 2582), (11060, 1000), (11073, 45),
  (11084, 438), (11372, 33), (11388, 776), (11603, 1451), (12107, 675),
  (12187, 119), (12200, 1005), (12259, 882), (12260, 999), (12364, 58),
  (12365, 74), (12541, 17), (12550, 217), (12698, 152), (12895, 1838)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0X0Y0_check. -/
theorem Z1Split72A0X0Y0_check : checkGrid m4TZ1 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0X0Y0_pairs. -/
theorem Z1Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split72A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0X0_pairs. -/
theorem Z1Split72A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0_pairs. -/
theorem Z1Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split72_check. -/
theorem Z1Split72_check : checkSplit m4TZ1 (2, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0X0Y0_check. -/
theorem Z1Split73A0X0Y0_check : checkGrid m4TZ1 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0X0Y0_pairs. -/
theorem Z1Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split73A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0X0_pairs. -/
theorem Z1Split73A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0_pairs. -/
theorem Z1Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split73_check. -/
theorem Z1Split73_check : checkSplit m4TZ1 (2, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split74A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X0Y0_check. -/
theorem Z1Split74A0X0Y0_check : checkGrid m4TZ1 3 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X0Y0_pairs. -/
theorem Z1Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split74A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X0_pairs. -/
theorem Z1Split74A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0_pairs. -/
theorem Z1Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split74A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split74_check. -/
theorem Z1Split74_check : checkSplit m4TZ1 (3, 0, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split74A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split75A0X0Y0Certs : List (Nat × Nat) := [
  (1271, 2571), (1278, 2201), (1283, 3167), (1320, 2918), (1326, 2921),
  (1349, 3241), (9484, 2400), (9780, 346), (9797, 3049), (9807, 825),
  (9872, 3135), (9881, 2513), (9882, 3029), (11389, 2683), (11470, 2402),
  (15438, 1263), (19788, 1743), (21637, 2516), (25393, 1934), (26937, 2554),
  (29627, 751), (29729, 3143), (31989, 3063), (32492, 840), (32513, 361),
  (32519, 717), (32616, 2413), (32627, 3201), (32628, 1530), (35729, 1240),
  (36264, 1489), (36406, 3068), (40032, 1352), (40037, 2498), (40049, 1622),
  (43670, 1026), (43672, 2239), (44138, 1551), (44250, 139), (47438, 1778),
  (47440, 2017), (47605, 1892), (47606, 490), (49091, 3038), (52146, 1244),
  (52320, 1666), (54524, 2522), (55095, 2197), (56312, 406), (56593, 3210),
  (60842, 3161), (60858, 2045), (60867, 2561), (61625, 1484), (62933, 1601),
  (63131, 297), (66676, 611), (66685, 2785), (66795, 858), (67476, 859),
  (67481, 1539), (67497, 880), (67590, 2487), (67602, 3088), (67613, 3141),
  (70590, 811), (71585, 1792), (71594, 2032), (71842, 1359), (71848, 495),
  (72773, 2551), (72911, 1218), (73701, 1259), (73773, 2415), (74002, 1400),
  (79773, 1548), (80907, 1706), (81464, 1226), (81466, 2881), (81508, 2689),
  (81725, 1112), (81748, 2706), (81869, 2389), (84017, 1598), (85193, 1747),
  (87432, 1264), (87602, 560), (91490, 3216), (92331, 1550), (94176, 955),
  (94549, 3080), (97834, 3212), (98911, 1482), (99882, 1279), (100267, 3090),
  (102302, 559), (103436, 2194), (103840, 1673), (103850, 2906), (104148, 337),
  (104198, 1120), (104216, 2214), (105537, 3150), (105707, 935), (107436, 1245),
  (110742, 1780), (113859, 3102), (116604, 1729), (116845, 3154), (117871, 2518)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X0Y0_check. -/
theorem Z1Split75A0X0Y0_check : checkGrid m4TZ1 3 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X0Y0_pairs. -/
theorem Z1Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 3 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split75A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X0_pairs. -/
theorem Z1Split75A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0_pairs. -/
theorem Z1Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split75A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split75_check. -/
theorem Z1Split75_check : checkSplit m4TZ1 (3, 1, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split75A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y0Certs : List (Nat × Nat) := [
  (5442, 399), (13377, 161), (16430, 142), (17487, 179), (21618, 212),
  (24871, 379), (28884, 307), (31404, 287), (31932, 295), (32606, 432),
  (39477, 146), (45463, 474), (46061, 558), (47210, 209), (51535, 419),
  (52645, 499), (53184, 512), (59036, 255), (61832, 461), (63630, 242),
  (80732, 431), (87399, 434), (93364, 292), (95173, 521), (101237, 449),
  (103127, 309), (107929, 485), (124640, 334), (129574, 133)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y0_check. -/
theorem Z1Split76A0X0Y0_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y0_pairs. -/
theorem Z1Split76A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y1Certs : List (Nat × Nat) := [
  (1795, 756), (3246, 696), (21310, 798), (23253, 714), (39315, 854),
  (58922, 580), (59577, 705), (59944, 579), (65524, 916), (71974, 768),
  (75984, 713), (76540, 748), (79208, 820), (81260, 823), (85215, 723),
  (86353, 808), (95227, 919), (99353, 574), (115867, 664), (116794, 606),
  (123010, 642)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y1_check. -/
theorem Z1Split76A0X0Y1_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y1_pairs. -/
theorem Z1Split76A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split76A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y2Certs : List (Nat × Nat) := [
  (1262, 1097), (18526, 994), (23871, 1183), (24116, 948), (71436, 1130),
  (76198, 1243), (76896, 995), (86735, 1061), (95978, 1084), (96673, 1239),
  (105034, 980), (106242, 1128), (106795, 1145), (110249, 1045), (111931, 1179),
  (116222, 1295), (117244, 1294), (119505, 1063), (125796, 1205), (129647, 998)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y2_check. -/
theorem Z1Split76A0X0Y2_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y2_pairs. -/
theorem Z1Split76A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split76A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y3Certs : List (Nat × Nat) := [
  (51, 1342), (12203, 1606), (19729, 1495), (21579, 1353), (48332, 1419),
  (54050, 1501), (62821, 1534), (65594, 1346), (72763, 1348), (87925, 1545),
  (116531, 1513), (119004, 1439)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y3_check. -/
theorem Z1Split76A0X0Y3_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y3_pairs. -/
theorem Z1Split76A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split76A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y4Certs : List (Nat × Nat) := [
  (406, 1932), (10217, 1993), (23938, 1923), (30098, 1929), (39583, 1750),
  (48133, 1661), (55032, 1832), (64704, 1770), (87172, 1734), (100196, 1904),
  (118716, 1947), (119227, 1946), (122817, 1950), (125022, 1709), (130867, 1882)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y4_check. -/
theorem Z1Split76A0X0Y4_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y4_pairs. -/
theorem Z1Split76A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split76A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y5Certs : List (Nat × Nat) := [
  (4262, 2182), (36282, 2403), (44155, 2150), (57308, 2421), (60107, 2203),
  (65686, 2171), (73318, 2142), (84436, 2414), (101220, 2316), (109047, 2430),
  (110411, 2284), (123228, 2303), (125615, 2191)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y5_check. -/
theorem Z1Split76A0X0Y5_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y5_pairs. -/
theorem Z1Split76A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split76A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y6Certs : List (Nat × Nat) := [
  (4306, 2593), (10518, 2639), (21240, 2626), (43167, 2558), (63943, 2765),
  (73693, 2776), (83821, 2691), (100223, 2699), (110724, 2544), (121434, 2493),
  (122666, 2651), (130066, 2458)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y6_check. -/
theorem Z1Split76A0X0Y6_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y6_pairs. -/
theorem Z1Split76A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split76A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y7Certs : List (Nat × Nat) := [
  (7945, 3110), (9001, 3188), (27371, 3067), (27912, 3101), (29220, 3022),
  (31986, 2966), (33800, 2806), (34982, 3051), (35729, 2850), (41041, 2971),
  (65014, 3089), (77352, 3069), (87568, 3238), (105964, 3097), (115514, 3105)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y7_check. -/
theorem Z1Split76A0X0Y7_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y7_pairs. -/
theorem Z1Split76A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split76A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0_pairs. -/
theorem Z1Split76A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split76A0X0Y0_pairs x hx y hy hw
  · exact Z1Split76A0X0Y1_pairs x hx y hy hw
  · exact Z1Split76A0X0Y2_pairs x hx y hy hw
  · exact Z1Split76A0X0Y3_pairs x hx y hy hw
  · exact Z1Split76A0X0Y4_pairs x hx y hy hw
  · exact Z1Split76A0X0Y5_pairs x hx y hy hw
  · exact Z1Split76A0X0Y6_pairs x hx y hy hw
  · exact Z1Split76A0X0Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y0Certs : List (Nat × Nat) := [
  (16301, 501), (49973, 390), (80474, 202), (81574, 286)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y0_check. -/
theorem Z1Split76A0X1Y0_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y0_pairs. -/
theorem Z1Split76A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y1Certs : List (Nat × Nat) := [
  (1206, 698), (5371, 747), (14480, 654), (19180, 733), (19823, 831),
  (31530, 770), (44873, 806), (45662, 624), (50487, 797), (67646, 607),
  (87153, 635)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y1_check. -/
theorem Z1Split76A0X1Y1_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y1_pairs. -/
theorem Z1Split76A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split76A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y2Certs : List (Nat × Nat) := [
  (8123, 1258), (20784, 1156), (22389, 1211), (27622, 1276), (29343, 1036),
  (42647, 1032), (45536, 1272), (70866, 1064), (79901, 936), (89267, 1049)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y2_check. -/
theorem Z1Split76A0X1Y2_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y2_pairs. -/
theorem Z1Split76A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split76A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y3Certs : List (Nat × Nat) := [
  (394, 1570), (3550, 1623), (8029, 1533), (8610, 1596), (13310, 1653),
  (24191, 1378), (25216, 1379), (28316, 1395), (43192, 1403), (45787, 1438),
  (48882, 1474), (54049, 1498), (58111, 1483), (58784, 1595), (74722, 1625),
  (80365, 1643), (83213, 1488)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y3_check. -/
theorem Z1Split76A0X1Y3_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y3_pairs. -/
theorem Z1Split76A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split76A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y4Certs : List (Nat × Nat) := [
  (8954, 1833), (20586, 1718), (21985, 1978), (27723, 1692), (33502, 1818),
  (38848, 1949), (49811, 1740), (70226, 1701), (72562, 1908)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y4_check. -/
theorem Z1Split76A0X1Y4_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y4_pairs. -/
theorem Z1Split76A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split76A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y5Certs : List (Nat × Nat) := [
  (2063, 2048), (4786, 2193), (22562, 2065), (24103, 2080), (25174, 2134),
  (34309, 2046), (37483, 2144), (44128, 2140), (52655, 2393), (61809, 2360),
  (63229, 2236), (66326, 2249), (67864, 2251), (70680, 2060), (71483, 2277),
  (72285, 2138), (77241, 2401), (78229, 2379), (85492, 2426)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y5_check. -/
theorem Z1Split76A0X1Y5_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y5_pairs. -/
theorem Z1Split76A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split76A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y6Certs : List (Nat × Nat) := [
  (2743, 2569), (5281, 2559), (11376, 2506), (14769, 2737), (28061, 2726),
  (29624, 2746), (36862, 2800), (37345, 2780), (37884, 2798), (43308, 2653),
  (48718, 2491), (52054, 2682), (52936, 2575), (56516, 2573), (61075, 2549),
  (63695, 2590), (89233, 2548)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y6_check. -/
theorem Z1Split76A0X1Y6_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y6_pairs. -/
theorem Z1Split76A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split76A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y7Certs : List (Nat × Nat) := [
  (38963, 3166), (39513, 2807), (47347, 3042), (51477, 2923), (52004, 2978),
  (54726, 3239), (61450, 2915), (70985, 2919), (72633, 3096), (72901, 2950),
  (75306, 2969), (77813, 3044), (78464, 3164), (80547, 2970), (81476, 2958),
  (84823, 2968)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y7_check. -/
theorem Z1Split76A0X1Y7_check : checkGrid m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y7_pairs. -/
theorem Z1Split76A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
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
      exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split76A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1_pairs. -/
theorem Z1Split76A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split76A0X1Y0_pairs x hx y hy hw
  · exact Z1Split76A0X1Y1_pairs x hx y hy hw
  · exact Z1Split76A0X1Y2_pairs x hx y hy hw
  · exact Z1Split76A0X1Y3_pairs x hx y hy hw
  · exact Z1Split76A0X1Y4_pairs x hx y hy hw
  · exact Z1Split76A0X1Y5_pairs x hx y hy hw
  · exact Z1Split76A0X1Y6_pairs x hx y hy hw
  · exact Z1Split76A0X1Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0_pairs. -/
theorem Z1Split76A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split76A0X0_pairs x hx y hy hw
  · exact Z1Split76A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split76_check. -/
theorem Z1Split76_check : checkSplit m4TZ1 (3, 2, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X0Y0Certs : List (Nat × Nat) := [
  (9243, 537), (15942, 1648), (18601, 2109), (18613, 2199), (19541, 2771),
  (19574, 3235), (43419, 2358), (65709, 129), (72598, 2627), (79520, 2297),
  (95888, 992), (96415, 1644), (102337, 546), (103312, 1187)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X0Y0_check. -/
theorem Z1Split77A0X0Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X0Y0_pairs. -/
theorem Z1Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X0_pairs. -/
theorem Z1Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X1Y0Certs : List (Nat × Nat) := [
  (8369, 507), (9313, 905), (9314, 908), (11361, 237), (20514, 332),
  (26257, 795), (30460, 76), (30521, 338), (31818, 299), (32114, 2375),
  (51772, 63), (53889, 2600), (54973, 812), (99304, 601)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X1Y0_check. -/
theorem Z1Split77A0X1Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X1Y0_pairs. -/
theorem Z1Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X1_pairs. -/
theorem Z1Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X2Y0Certs : List (Nat × Nat) := [
  (2171, 3151), (5198, 2964), (31456, 684), (31737, 2979), (56512, 2694),
  (56986, 37), (57062, 356), (57127, 699), (57149, 818), (57155, 865),
  (57418, 3177), (63595, 386), (80603, 614), (91328, 2965), (97344, 2156),
  (99019, 1615), (104783, 2596)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X2Y0_check. -/
theorem Z1Split77A0X2Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X2Y0_pairs. -/
theorem Z1Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk2 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X2_pairs. -/
theorem Z1Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X3Y0Certs : List (Nat × Nat) := [
  (16277, 923), (21600, 1665), (22358, 891), (24659, 1829), (27577, 889),
  (28314, 196), (34232, 1845), (49765, 897), (50683, 1215), (52279, 372),
  (75319, 302), (81119, 1141), (82939, 1680), (82940, 1686), (85141, 1910),
  (85827, 637), (93287, 1023)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X3Y0_check. -/
theorem Z1Split77A0X3Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X3Y0_pairs. -/
theorem Z1Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk3 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X3_pairs. -/
theorem Z1Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X4Y0Certs : List (Nat × Nat) := [
  (7555, 804), (18306, 191), (25712, 226), (25828, 813), (27555, 755),
  (27825, 3012), (53562, 282), (53658, 787), (63615, 530), (66895, 2167),
  (69747, 721), (69765, 834), (69855, 1467), (69951, 2349), (70006, 2945),
  (70008, 2948), (71815, 198), (80114, 350), (82335, 593)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X4Y0_check. -/
theorem Z1Split77A0X4Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X4Y0_pairs. -/
theorem Z1Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk4 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X4_pairs. -/
theorem Z1Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X5Y0Certs : List (Nat × Nat) := [
  (23723, 1311), (23733, 1351), (61935, 833), (62176, 2944), (63315, 1334),
  (70977, 340), (71274, 2445), (76248, 598), (76420, 1736), (83444, 2376),
  (86519, 2635), (91004, 429)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X5Y0_check. -/
theorem Z1Split77A0X5Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X5Y0_pairs. -/
theorem Z1Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk5 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X5_pairs. -/
theorem Z1Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X6Y0Certs : List (Nat × Nat) := [
  (7560, 832), (7665, 1543), (7748, 2354), (7752, 2366), (7801, 2943),
  (7807, 2960), (10792, 2351), (19660, 389), (19751, 900), (21466, 762),
  (21988, 1323), (22029, 1639), (38862, 719), (38970, 1466), (79454, 1659),
  (80492, 109), (80611, 687), (80645, 863), (80728, 1460), (80740, 1506),
  (80892, 2982), (90229, 932), (109074, 2056)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X6Y0_check. -/
theorem Z1Split77A0X6Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X6Y0_pairs. -/
theorem Z1Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk6 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X6_pairs. -/
theorem Z1Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X7Y0Certs : List (Nat × Nat) := [
  (11295, 3013), (17652, 1433), (19488, 2270), (19749, 893), (19768, 1014),
  (22430, 1361), (29647, 326), (40979, 428), (50425, 2741), (51090, 1019),
  (54292, 2352), (54982, 890), (57999, 710), (62242, 194), (62539, 2129),
  (62693, 247), (65499, 1398), (95993, 1723), (102977, 1926), (103036, 2557)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X7Y0_check. -/
theorem Z1Split77A0X7Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X7Y0_pairs. -/
theorem Z1Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X7Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk7 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X7_pairs. -/
theorem Z1Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X8Y0Certs : List (Nat × Nat) := [
  (2681, 339), (10604, 815), (10873, 3174), (12493, 1887), (61413, 369),
  (66494, 2500), (66538, 2994), (75881, 1010), (75915, 1233), (77537, 535),
  (87555, 594), (87561, 608), (89376, 1047), (89448, 1605)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X8Y0_check. -/
theorem Z1Split77A0X8Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X8Y0_pairs. -/
theorem Z1Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X8Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk8 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X8_pairs. -/
theorem Z1Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X9Y0Certs : List (Nat × Nat) := [
  (10892, 106), (11023, 730), (11039, 816), (11140, 1507), (11146, 1568),
  (11308, 3175), (15661, 38), (15802, 700), (35710, 201), (35783, 549),
  (39361, 1167), (39454, 1850), (40667, 1171), (42803, 892), (45890, 1180),
  (50082, 283), (50086, 289), (50178, 785), (50295, 1541), (50382, 2367),
  (50433, 2949), (54489, 556), (66336, 1185), (67592, 851), (68365, 336),
  (70703, 1310)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X9Y0_check. -/
theorem Z1Split77A0X9Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X9Y0_pairs. -/
theorem Z1Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X9Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk9 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X9_pairs. -/
theorem Z1Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X10Y0Certs : List (Nat × Nat) := [
  (504, 331), (40077, 281), (40097, 355), (40173, 786), (40394, 2503),
  (40432, 2961), (40438, 2993), (43419, 2357), (46094, 3008), (50870, 2953),
  (67609, 930), (67711, 1670), (68261, 2772), (70744, 1614), (71364, 131),
  (71678, 2149), (97710, 1542), (97797, 2368)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X10Y0_check. -/
theorem Z1Split77A0X10Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X10Y0_pairs. -/
theorem Z1Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X10Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk10 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X10_pairs. -/
theorem Z1Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X11Y0Certs : List (Nat × Nat) := [
  (1081, 1168), (31849, 446), (33132, 343), (33207, 720), (33313, 1461),
  (33315, 1465), (33413, 2353), (33429, 2448), (45100, 1738), (50292, 1522),
  (71394, 252), (72752, 534), (74056, 533), (74071, 595), (77376, 2588),
  (101556, 1048), (106684, 539), (106685, 542)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X11Y0_check. -/
theorem Z1Split77A0X11Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X11Y0_pairs. -/
theorem Z1Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X11Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk11 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X11_pairs. -/
theorem Z1Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X12Y0Certs : List (Nat × Nat) := [
  (217, 1186), (761, 2093), (2531, 2365), (2744, 649), (3763, 1651),
  (3787, 1857), (8175, 2216), (17992, 794), (34553, 991), (47313, 2119),
  (49030, 1875), (51070, 896), (53045, 2954), (53785, 1645), (57310, 2091),
  (82346, 633), (84646, 1470), (97942, 327)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X12Y0_check. -/
theorem Z1Split77A0X12Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X12Y0_pairs. -/
theorem Z1Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X12Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk12 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X12_pairs. -/
theorem Z1Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X13Y0Certs : List (Nat × Nat) := [
  (6280, 1007), (17127, 809), (18777, 341), (18841, 685), (18976, 1567),
  (19056, 2350), (19074, 2446), (19122, 2980), (26987, 108), (27235, 1505),
  (52096, 2108), (57969, 554), (58079, 1222), (63082, 62), (63462, 2624),
  (65266, 105), (67707, 1649), (72691, 224), (77431, 35), (77491, 291),
  (77572, 701), (77578, 731), (77804, 2502), (77848, 2996), (84615, 1234),
  (99894, 1641)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X13Y0_check. -/
theorem Z1Split77A0X13Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X13Y0_pairs. -/
theorem Z1Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X13Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk13 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X13_pairs. -/
theorem Z1Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X14Y0Certs : List (Nat × Nat) := [
  (24955, 803), (31136, 1409), (37056, 373), (37366, 2641), (38292, 81),
  (47351, 2478), (54961, 763), (64145, 1039), (90615, 661), (92033, 1391),
  (92871, 1184), (94618, 1216), (95044, 1178), (95065, 1315), (97310, 1853),
  (99650, 175), (102029, 1329)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X14Y0_check. -/
theorem Z1Split77A0X14Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X14Y0_pairs. -/
theorem Z1Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X14Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk14 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X14_pairs. -/
theorem Z1Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X15Y0Certs : List (Nat × Nat) := [
  (5298, 370), (20309, 1828), (22108, 2373), (23807, 1927), (30234, 1196),
  (30235, 1201), (34038, 536), (36619, 371), (36989, 83), (39131, 2976),
  (49191, 192), (74481, 450), (76672, 545), (77389, 2672), (79455, 1664),
  (80974, 301), (81819, 197)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X15Y0_check. -/
theorem Z1Split77A0X15Y0_check : checkGrid m4TZ1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X15Y0_pairs. -/
theorem Z1Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X15Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk15 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X15_pairs. -/
theorem Z1Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0_pairs. -/
theorem Z1Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split77A0X0_pairs x hx y hy hw
  · exact Z1Split77A0X1_pairs x hx y hy hw
  · exact Z1Split77A0X2_pairs x hx y hy hw
  · exact Z1Split77A0X3_pairs x hx y hy hw
  · exact Z1Split77A0X4_pairs x hx y hy hw
  · exact Z1Split77A0X5_pairs x hx y hy hw
  · exact Z1Split77A0X6_pairs x hx y hy hw
  · exact Z1Split77A0X7_pairs x hx y hy hw
  · exact Z1Split77A0X8_pairs x hx y hy hw
  · exact Z1Split77A0X9_pairs x hx y hy hw
  · exact Z1Split77A0X10_pairs x hx y hy hw
  · exact Z1Split77A0X11_pairs x hx y hy hw
  · exact Z1Split77A0X12_pairs x hx y hy hw
  · exact Z1Split77A0X13_pairs x hx y hy hw
  · exact Z1Split77A0X14_pairs x hx y hy hw
  · exact Z1Split77A0X15_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split77_check. -/
theorem Z1Split77_check : checkSplit m4TZ1 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split78A0X0Y0Certs : List (Nat × Nat) := [
  (1286, 2087), (1348, 2579), (6644, 440), (7075, 1837), (9785, 75),
  (9878, 153), (13860, 2), (14766, 95), (19290, 12), (19292, 32),
  (19308, 775), (24938, 150), (25010, 1001), (26548, 2577), (29801, 261),
  (31523, 1453), (32500, 218), (32624, 442), (35531, 272), (35537, 678),
  (35549, 2941), (40042, 1308), (41028, 779), (41102, 25), (43182, 318),
  (43655, 69), (43657, 115), (46596, 88), (46602, 321), (46608, 783),
  (47452, 1305), (47454, 1630), (47590, 220), (47593, 366), (51630, 4),
  (51632, 22), (51636, 94), (60865, 1842), (63179, 2942), (63287, 671),
  (66087, 2345), (66664, 53), (66668, 149), (67486, 590), (67610, 1004),
  (69893, 1449), (69897, 2339), (69899, 2932), (71601, 1160), (71605, 1841),
  (71829, 186), (71834, 439), (72581, 274), (72587, 670), (72593, 1458),
  (79560, 9), (79572, 312), (79578, 784), (81453, 43), (81476, 2081),
  (81736, 588), (81739, 886), (86762, 23), (86766, 93), (86772, 320),
  (92170, 223), (95692, 1303), (101141, 266), (101157, 2343), (101159, 2937),
  (103831, 16), (103858, 2576), (104205, 526), (104210, 1006), (105197, 681),
  (105203, 1447), (105207, 2335), (117545, 72), (117736, 587), (120686, 2082)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X0Y0_check. -/
theorem Z1Split78A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X0Y0_pairs. -/
theorem Z1Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split78A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X0_pairs. -/
theorem Z1Split78A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0_pairs. -/
theorem Z1Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split78A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split78_check. -/
theorem Z1Split78_check : checkSplit m4TZ1 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X0Y0_check. -/
theorem Z1Split79A0X0Y0_check : checkGrid m4TZ1 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X0Y0_pairs. -/
theorem Z1Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split79A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X0_pairs. -/
theorem Z1Split79A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0_pairs. -/
theorem Z1Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split79A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split79_check. -/
theorem Z1Split79_check : checkSplit m4TZ1 (3, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split79A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split80A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y0_check. -/
theorem Z1Split80A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0Y0_pairs. -/
theorem Z1Split80A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split80A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks4S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks4S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S32768Chunk0_bound
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
      exact Z1M2Right_bound y (masks4S32768Chunk0_bound y hy)
  · exact Z1Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split80A0X0_pairs. -/
theorem Z1Split80A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split80A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split81A0X0Y0Certs : List (Nat × Nat) := [
  (3347, 2638), (3529, 2773), (4532, 544), (8989, 814), (11075, 2377),
  (14139, 1603), (17642, 1212), (20727, 500), (20843, 577), (23229, 2359),
  (25011, 650), (28111, 3015), (31644, 2556), (32610, 232), (32704, 333),
  (33549, 942), (37423, 837), (41890, 1129), (42117, 1284), (44279, 2967),
  (47321, 2141), (47918, 2570), (49937, 1054), (50452, 1411), (56788, 3181),
  (57447, 625), (57681, 805), (59069, 1762), (61722, 796), (65310, 433),
  (67216, 1810), (67533, 2047), (69771, 735), (72770, 3014), (75550, 1936),
  (75986, 2301), (80856, 2991), (81522, 400), (82866, 1380), (83713, 1967),
  (85345, 195), (90440, 996), (91929, 2100), (92972, 2922), (94585, 1050),
  (95314, 1572), (98209, 753), (102576, 949), (104343, 2252), (104798, 2604),
  (105670, 210), (107858, 1834), (109600, 3236), (112072, 1930), (112665, 2423),
  (113998, 393), (115920, 1771), (116438, 2200), (121291, 2777), (121627, 3100)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0Y0_check. -/
theorem Z1Split81A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0Y0_pairs. -/
theorem Z1Split81A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split81A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S256Chunk0 masks3S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
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
      exact Z1M2Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact Z1Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split81A0X0_pairs. -/
theorem Z1Split81A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split81A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
  (108128, 1392), (110229, 894), (111077, 767)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X0Y0_check. -/
theorem Z1Split82A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X0Y0_pairs. -/
theorem Z1Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X0Y0Certs
  · decide
  · decide
  · decide
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split82A0X1Y0Certs : List (Nat × Nat) := [
  (267, 1523), (1225, 2361), (1339, 173), (1563, 1475), (2780, 864),
  (3308, 1496), (4221, 1856), (6021, 2418), (6562, 193), (10908, 165),
  (12404, 1221), (13279, 1269), (15951, 1699), (16239, 709), (16678, 732),
  (17496, 451), (19418, 1637), (19852, 1635), (20312, 1846), (20645, 1038),
  (20902, 121), (23377, 1987), (24654, 1733), (25182, 2623), (27288, 1931),
  (28831, 596), (28896, 947), (28903, 1015), (32006, 1410), (33082, 122),
  (35136, 2139), (35713, 208), (36716, 902), (37664, 1463), (38684, 2832),
  (40368, 2271), (41434, 540), (42478, 1652), (43856, 2364), (44210, 1621),
  (44741, 2479), (46090, 2972), (46648, 503), (46906, 2380), (48103, 1462),
  (48652, 2422), (49545, 2637), (51322, 3093), (53448, 2584), (53958, 111),
  (54819, 66), (56064, 2601), (56431, 1911), (57067, 378), (59999, 2835),
  (60903, 49), (61448, 551), (64615, 1316), (64677, 1769), (64687, 1858),
  (65411, 807), (66339, 1197), (67941, 374), (70016, 2977), (70847, 2568),
  (71336, 3153), (72326, 565), (73288, 1135), (73502, 3023), (74738, 2355),
  (75248, 3099), (76616, 279)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X1Y0_check. -/
theorem Z1Split82A0X1Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split82A0X1Y0_pairs. -/
theorem Z1Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split82A0X1Y0Certs
  · decide
  · decide
  · decide
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split83A0X0Y0Certs : List (Nat × Nat) := [
  (660, 0), (4409, 2929), (7172, 21), (11898, 773), (15262, 1301),
  (19451, 262), (26736, 90), (27642, 313), (31975, 1835), (37200, 6),
  (39948, 774), (43946, 2083), (51827, 672), (51935, 70), (57311, 265),
  (65159, 2936), (66748, 2580), (72698, 151), (75152, 28), (78417, 2341),
  (80600, 1002), (86963, 1455), (87130, 222), (95567, 677), (99162, 322),
  (99526, 591), (105434, 441), (107916, 99), (115107, 2346), (120563, 1459)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X0Y0_check. -/
theorem Z1Split83A0X0Y0_check : checkGrid m4TZ1 2 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X0Y0_pairs. -/
theorem Z1Split83A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split83A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
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
      exact Z1M2Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0X0_pairs. -/
theorem Z1Split83A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split83A0_pairs. -/
theorem Z1Split83A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split83A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X0Y0_check. -/
theorem Z1Split84A0X0Y0_check : checkGrid m4TZ1 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X0Y0_pairs. -/
theorem Z1Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split84A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks4S32768Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks4S32768Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0X0_pairs. -/
theorem Z1Split84A0X0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split84A0_pairs. -/
theorem Z1Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split84A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split85A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0Y0_check. -/
theorem Z1Split85A0X0Y0_check : checkGrid m4TZ1 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0Y0_pairs. -/
theorem Z1Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split85A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
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
      exact Z1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z1Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split85A0X0_pairs. -/
theorem Z1Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split85A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split86A0X0Y0Certs : List (Nat × Nat) := [
  (259, 1476), (1233, 2390), (2513, 2146), (3034, 3039), (3867, 2622),
  (4526, 899), (5044, 1477), (5275, 275), (6203, 548), (7246, 1668),
  (7758, 2391), (7968, 688), (8924, 1220), (9693, 599), (10429, 3040),
  (11066, 1012), (11548, 1324), (11800, 276), (12484, 1852), (12753, 690)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split86A0X0Y0_check. -/
theorem Z1Split86A0X0Y0_check : checkGrid m4TZ1 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split86A0X0Y0_pairs. -/
theorem Z1Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split86A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
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
      exact Z1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z1Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split86A0X0_pairs. -/
theorem Z1Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0X0Y0_check. -/
theorem Z1Split87A0X0Y0_check : checkGrid m4TZ1 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0X0Y0_pairs. -/
theorem Z1Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split87A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
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
      exact Z1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0X0_pairs. -/
theorem Z1Split87A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split87A0_pairs. -/
theorem Z1Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split88A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X0Y0_check. -/
theorem Z1Split88A0X0Y0_check : checkGrid m4TZ1 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X0Y0_pairs. -/
theorem Z1Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split88A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
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
      exact Z1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0X0_pairs. -/
theorem Z1Split88A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split88A0_pairs. -/
theorem Z1Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split88A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split89A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split89A0X0Y0_check. -/
theorem Z1Split89A0X0Y0_check : checkGrid m4TZ1 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split89A0X0Y0_pairs. -/
theorem Z1Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split89A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
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
      exact Z1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z1Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split89A0X0_pairs. -/
theorem Z1Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split90A0X0Y0Certs : List (Nat × Nat) := [
  (162, 310), (267, 2334), (318, 771), (449, 2930), (480, 3),
  (611, 263), (662, 26), (767, 673), (786, 96), (863, 1456)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0X0Y0_check. -/
theorem Z1Split90A0X0Y0_check : checkGrid m4TZ1 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0X0Y0_pairs. -/
theorem Z1Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split90A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z1Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0X0_pairs. -/
theorem Z1Split90A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split90A0_pairs. -/
theorem Z1Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0X0Y0_check. -/
theorem Z1Split91A0X0Y0_check : checkGrid m4TZ1 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0X0Y0_pairs. -/
theorem Z1Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split91A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0X0_pairs. -/
theorem Z1Split91A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split91A0_pairs. -/
theorem Z1Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0X0Y0_check. -/
theorem Z1Split92A0X0Y0_check : checkGrid m4TZ1 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0X0Y0_pairs. -/
theorem Z1Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split92A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z1Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0X0_pairs. -/
theorem Z1Split92A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split92A0_pairs. -/
theorem Z1Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0X0Y0_check. -/
theorem Z1Split93A0X0Y0_check : checkGrid m4TZ1 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0X0Y0_pairs. -/
theorem Z1Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split93A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z1Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0X0_pairs. -/
theorem Z1Split93A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split93A0_pairs. -/
theorem Z1Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 7 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0X0Y0_check. -/
theorem Z1Split94A0X0Y0_check : checkGrid m4TZ1 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0X0Y0_pairs. -/
theorem Z1Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 8 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split94A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z1Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0X0_pairs. -/
theorem Z1Split94A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 8 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z1Split94A0_pairs. -/
theorem Z1Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 8 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for checkAll_Z1. -/
theorem checkAll_Z1 : checkAll m4TZ1 splitsZ1 = true := by
  simp only [checkAll, splitsZ1, List.all_cons, List.all_nil,
    Z1Split0_check, Z1Split1_check, Z1Split2_check, Z1Split3_check,
    Z1Split4_check, Z1Split5_check, Z1Split6_check, Z1Split7_check,
    Z1Split8_check, Z1Split9_check, Z1Split10_check, Z1Split11_check,
    Z1Split12_check, Z1Split13_check, Z1Split14_check, Z1Split15_check,
    Z1Split16_check, Z1Split17_check, Z1Split18_check, Z1Split19_check,
    Z1Split20_check, Z1Split21_check, Z1Split22_check, Z1Split23_check,
    Z1Split24_check, Z1Split25_check, Z1Split26_check, Z1Split27_check,
    Z1Split28_check, Z1Split29_check, Z1Split30_check, Z1Split31_check,
    Z1Split32_check, Z1Split33_check, Z1Split34_check, Z1Split35_check,
    Z1Split36_check, Z1Split37_check, Z1Split38_check, Z1Split39_check,
    Z1Split40_check, Z1Split41_check, Z1Split42_check, Z1Split43_check,
    Z1Split44_check, Z1Split45_check, Z1Split46_check, Z1Split47_check,
    Z1Split48_check, Z1Split49_check, Z1Split50_check, Z1Split51_check,
    Z1Split52_check, Z1Split53_check, Z1Split54_check, Z1Split55_check,
    Z1Split56_check, Z1Split57_check, Z1Split58_check, Z1Split59_check,
    Z1Split60_check, Z1Split61_check, Z1Split62_check, Z1Split63_check,
    Z1Split64_check, Z1Split65_check, Z1Split66_check, Z1Split67_check,
    Z1Split68_check, Z1Split69_check, Z1Split70_check, Z1Split71_check,
    Z1Split72_check, Z1Split73_check, Z1Split74_check, Z1Split75_check,
    Z1Split76_check, Z1Split77_check, Z1Split78_check, Z1Split79_check,
    Z1Split80_check, Z1Split81_check, Z1Split82_check, Z1Split83_check,
    Z1Split84_check, Z1Split85_check, Z1Split86_check, Z1Split87_check,
    Z1Split88_check, Z1Split89_check, Z1Split90_check, Z1Split91_check,
    Z1Split92_check, Z1Split93_check, Z1Split94_check, Bool.and_true]

#print axioms checkAll_Z1

end Quantum.Stabilizer.Homological.LP.M150

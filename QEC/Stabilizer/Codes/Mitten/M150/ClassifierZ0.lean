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
def Z0Split0A0X0Y0Certs : List (Nat × Nat) := [
  (0, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split0A0X0Y0_check. -/
theorem Z0Split0A0X0Y0_check : checkGrid m4TZ0 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split0A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split0A0X0Y0_pairs. -/
theorem Z0Split0A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 0 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split0A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split0A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split0A0X0_pairs. -/
theorem Z0Split0A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 0 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split0A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split0A0_pairs. -/
theorem Z0Split0A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 0 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split0A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split0_check. -/
theorem Z0Split0_check : checkSplit m4TZ0 (0, 0, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split0A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split1A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A0X0Y0_check. -/
theorem Z0Split1A0X0Y0_check : checkGrid m4TZ0 3 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A0X0Y0_pairs. -/
theorem Z0Split1A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 2 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split1A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A0X0_pairs. -/
theorem Z0Split1A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 2 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split1A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A0_pairs. -/
theorem Z0Split1A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 2 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split1A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split1A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A1X0Y0_check. -/
theorem Z0Split1A1X0Y0_check : checkGrid m4TZ0 3 376821623 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A1X0Y0_pairs. -/
theorem Z0Split1A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 2 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split1A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A1X0_pairs. -/
theorem Z0Split1A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 2 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split1A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A1_pairs. -/
theorem Z0Split1A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 2 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split1A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split1A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A2X0Y0_check. -/
theorem Z0Split1A2X0Y0_check : checkGrid m4TZ0 3 768556269 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A2X0Y0_pairs. -/
theorem Z0Split1A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 2 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split1A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A2X0_pairs. -/
theorem Z0Split1A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 2 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split1A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A2_pairs. -/
theorem Z0Split1A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 2 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split1A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split1A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A3X0Y0_check. -/
theorem Z0Split1A3X0Y0_check : checkGrid m4TZ0 3 1002105754 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A3X0Y0_pairs. -/
theorem Z0Split1A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 2 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split1A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split1A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A3X0_pairs. -/
theorem Z0Split1A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 2 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split1A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1A3_pairs. -/
theorem Z0Split1A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 2 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split1A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split1_check. -/
theorem Z0Split1_check : checkSplit m4TZ0 (0, 0, 2, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split1A0_pairs x hx y hy hw
    · exact Z0Split1A1_pairs x hx y hy hw
    · exact Z0Split1A2_pairs x hx y hy hw
    · exact Z0Split1A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split2A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split2A0X0Y0_check. -/
theorem Z0Split2A0X0Y0_check : checkGrid m4TZ0 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split2A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split2A0X0Y0_pairs. -/
theorem Z0Split2A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 1 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split2A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split2A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split2A0X0_pairs. -/
theorem Z0Split2A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 1 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split2A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split2A0_pairs. -/
theorem Z0Split2A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 1 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split2A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split2_check. -/
theorem Z0Split2_check : checkSplit m4TZ0 (0, 1, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split2A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split3A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split3A0X0Y0_check. -/
theorem Z0Split3A0X0Y0_check : checkGrid m4TZ0 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split3A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split3A0X0Y0_pairs. -/
theorem Z0Split3A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split3A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split3A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split3A0X0_pairs. -/
theorem Z0Split3A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split3A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split3A0_pairs. -/
theorem Z0Split3A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split3A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split3_check. -/
theorem Z0Split3_check : checkSplit m4TZ0 (0, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split3A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split4A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split4A0X0Y0_check. -/
theorem Z0Split4A0X0Y0_check : checkGrid m4TZ0 2 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split4A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split4A0X0Y0_pairs. -/
theorem Z0Split4A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 1 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split4A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split4A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split4A0X0_pairs. -/
theorem Z0Split4A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 1 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split4A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split4A0_pairs. -/
theorem Z0Split4A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 1 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split4A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split4_check. -/
theorem Z0Split4_check : checkSplit m4TZ0 (1, 0, 1, 2) = true := by
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
    · exact Z0Split4A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split5A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split5A0X0Y0_check. -/
theorem Z0Split5A0X0Y0_check : checkGrid m4TZ0 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split5A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split5A0X0Y0_pairs. -/
theorem Z0Split5A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 1 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split5A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split5A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split5A0X0_pairs. -/
theorem Z0Split5A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 1 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split5A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split5A0_pairs. -/
theorem Z0Split5A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 1 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split5A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split5_check. -/
theorem Z0Split5_check : checkSplit m4TZ0 (1, 1, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split5A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split6A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split6A0X0Y0_check. -/
theorem Z0Split6A0X0Y0_check : checkGrid m4TZ0 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split6A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split6A0X0Y0_pairs. -/
theorem Z0Split6A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split6A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split6A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split6A0X0_pairs. -/
theorem Z0Split6A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split6A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split6A0_pairs. -/
theorem Z0Split6A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split6A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split6_check. -/
theorem Z0Split6_check : checkSplit m4TZ0 (2, 0, 0, 2) = true := by
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
    · exact Z0Split6A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split7A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A0X0Y0_check. -/
theorem Z0Split7A0X0Y0_check : checkGrid m4TZ0 3 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A0X0Y0_pairs. -/
theorem Z0Split7A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split7A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A0X0_pairs. -/
theorem Z0Split7A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split7A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A0_pairs. -/
theorem Z0Split7A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split7A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split7A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A1X0Y0_check. -/
theorem Z0Split7A1X0Y0_check : checkGrid m4TZ0 3 376821623 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A1X0Y0_pairs. -/
theorem Z0Split7A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split7A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A1X0_pairs. -/
theorem Z0Split7A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split7A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A1_pairs. -/
theorem Z0Split7A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split7A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split7A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A2X0Y0_check. -/
theorem Z0Split7A2X0Y0_check : checkGrid m4TZ0 3 768556269 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A2X0Y0_pairs. -/
theorem Z0Split7A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split7A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A2X0_pairs. -/
theorem Z0Split7A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split7A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A2_pairs. -/
theorem Z0Split7A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split7A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split7A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A3X0Y0_check. -/
theorem Z0Split7A3X0Y0_check : checkGrid m4TZ0 3 1002105754 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A3X0Y0_pairs. -/
theorem Z0Split7A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split7A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split7A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A3X0_pairs. -/
theorem Z0Split7A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split7A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7A3_pairs. -/
theorem Z0Split7A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split7A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split7_check. -/
theorem Z0Split7_check : checkSplit m4TZ0 (0, 0, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split7A0_pairs x hx y hy hw
    · exact Z0Split7A1_pairs x hx y hy hw
    · exact Z0Split7A2_pairs x hx y hy hw
    · exact Z0Split7A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split8A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A0X0Y0_check. -/
theorem Z0Split8A0X0Y0_check : checkGrid m4TZ0 3 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A0X0Y0_pairs. -/
theorem Z0Split8A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split8A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A0X0_pairs. -/
theorem Z0Split8A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split8A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A0_pairs. -/
theorem Z0Split8A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split8A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split8A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A1X0Y0_check. -/
theorem Z0Split8A1X0Y0_check : checkGrid m4TZ0 3 376821623 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A1X0Y0_pairs. -/
theorem Z0Split8A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split8A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A1X0_pairs. -/
theorem Z0Split8A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split8A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A1_pairs. -/
theorem Z0Split8A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split8A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split8A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A2X0Y0_check. -/
theorem Z0Split8A2X0Y0_check : checkGrid m4TZ0 3 768556269 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A2X0Y0_pairs. -/
theorem Z0Split8A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split8A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A2X0_pairs. -/
theorem Z0Split8A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split8A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A2_pairs. -/
theorem Z0Split8A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split8A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split8A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A3X0Y0_check. -/
theorem Z0Split8A3X0Y0_check : checkGrid m4TZ0 3 1002105754 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A3X0Y0_pairs. -/
theorem Z0Split8A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split8A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split8A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A3X0_pairs. -/
theorem Z0Split8A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split8A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8A3_pairs. -/
theorem Z0Split8A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split8A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split8_check. -/
theorem Z0Split8_check : checkSplit m4TZ0 (0, 1, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split8A0_pairs x hx y hy hw
    · exact Z0Split8A1_pairs x hx y hy hw
    · exact Z0Split8A2_pairs x hx y hy hw
    · exact Z0Split8A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split9A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split9A0X0Y0_check. -/
theorem Z0Split9A0X0Y0_check : checkGrid m4TZ0 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split9A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split9A0X0Y0_pairs. -/
theorem Z0Split9A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split9A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split9A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split9A0X0_pairs. -/
theorem Z0Split9A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split9A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split9A0_pairs. -/
theorem Z0Split9A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split9A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split9_check. -/
theorem Z0Split9_check : checkSplit m4TZ0 (0, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split9A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split10A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split10A0X0Y0_check. -/
theorem Z0Split10A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split10A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split10A0X0Y0_pairs. -/
theorem Z0Split10A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split10A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split10A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split10A0X0_pairs. -/
theorem Z0Split10A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split10A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split10A0_pairs. -/
theorem Z0Split10A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split10A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split10_check. -/
theorem Z0Split10_check : checkSplit m4TZ0 (0, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split10A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split11A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split11A0X0Y0_check. -/
theorem Z0Split11A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split11A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split11A0X0Y0_pairs. -/
theorem Z0Split11A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split11A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split11A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split11A0X0_pairs. -/
theorem Z0Split11A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split11A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split11A0_pairs. -/
theorem Z0Split11A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split11A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split11_check. -/
theorem Z0Split11_check : checkSplit m4TZ0 (0, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split11A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split12A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A0X0Y0_check. -/
theorem Z0Split12A0X0Y0_check : checkGrid m4TZ0 3 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A0X0Y0_pairs. -/
theorem Z0Split12A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split12A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A0X0_pairs. -/
theorem Z0Split12A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split12A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A0_pairs. -/
theorem Z0Split12A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split12A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split12A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A1X0Y0_check. -/
theorem Z0Split12A1X0Y0_check : checkGrid m4TZ0 3 376821623 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A1X0Y0_pairs. -/
theorem Z0Split12A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split12A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A1X0_pairs. -/
theorem Z0Split12A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split12A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A1_pairs. -/
theorem Z0Split12A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split12A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split12A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A2X0Y0_check. -/
theorem Z0Split12A2X0Y0_check : checkGrid m4TZ0 3 768556269 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A2X0Y0_pairs. -/
theorem Z0Split12A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split12A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A2X0_pairs. -/
theorem Z0Split12A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split12A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A2_pairs. -/
theorem Z0Split12A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split12A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split12A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A3X0Y0_check. -/
theorem Z0Split12A3X0Y0_check : checkGrid m4TZ0 3 1002105754 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A3X0Y0_pairs. -/
theorem Z0Split12A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split12A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split12A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A3X0_pairs. -/
theorem Z0Split12A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split12A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12A3_pairs. -/
theorem Z0Split12A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split12A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split12_check. -/
theorem Z0Split12_check : checkSplit m4TZ0 (1, 0, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split12A0_pairs x hx y hy hw
    · exact Z0Split12A1_pairs x hx y hy hw
    · exact Z0Split12A2_pairs x hx y hy hw
    · exact Z0Split12A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split13A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A0X0Y0_check. -/
theorem Z0Split13A0X0Y0_check : checkGrid m4TZ0 3 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A0X0Y0_pairs. -/
theorem Z0Split13A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 2 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split13A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A0X0_pairs. -/
theorem Z0Split13A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 2 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split13A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A0_pairs. -/
theorem Z0Split13A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 2 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split13A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split13A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A1X0Y0_check. -/
theorem Z0Split13A1X0Y0_check : checkGrid m4TZ0 3 376821623 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A1X0Y0_pairs. -/
theorem Z0Split13A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 2 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split13A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A1X0_pairs. -/
theorem Z0Split13A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 2 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split13A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A1_pairs. -/
theorem Z0Split13A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 2 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split13A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split13A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A2X0Y0_check. -/
theorem Z0Split13A2X0Y0_check : checkGrid m4TZ0 3 768556269 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A2X0Y0_pairs. -/
theorem Z0Split13A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 2 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split13A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A2X0_pairs. -/
theorem Z0Split13A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 2 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split13A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A2_pairs. -/
theorem Z0Split13A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 2 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split13A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split13A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A3X0Y0_check. -/
theorem Z0Split13A3X0Y0_check : checkGrid m4TZ0 3 1002105754 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A3X0Y0_pairs. -/
theorem Z0Split13A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 2 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split13A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split13A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A3X0_pairs. -/
theorem Z0Split13A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 2 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split13A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13A3_pairs. -/
theorem Z0Split13A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 2 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split13A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split13_check. -/
theorem Z0Split13_check : checkSplit m4TZ0 (1, 1, 2, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split13A0_pairs x hx y hy hw
    · exact Z0Split13A1_pairs x hx y hy hw
    · exact Z0Split13A2_pairs x hx y hy hw
    · exact Z0Split13A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split14A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split14A0X0Y0_check. -/
theorem Z0Split14A0X0Y0_check : checkGrid m4TZ0 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split14A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split14A0X0Y0_pairs. -/
theorem Z0Split14A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split14A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split14A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split14A0X0_pairs. -/
theorem Z0Split14A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split14A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split14A0_pairs. -/
theorem Z0Split14A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split14A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split14_check. -/
theorem Z0Split14_check : checkSplit m4TZ0 (1, 2, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split14A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split15A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split15A0X0Y0_check. -/
theorem Z0Split15A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split15A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split15A0X0Y0_pairs. -/
theorem Z0Split15A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split15A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split15A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split15A0X0_pairs. -/
theorem Z0Split15A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split15A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split15A0_pairs. -/
theorem Z0Split15A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split15A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split15_check. -/
theorem Z0Split15_check : checkSplit m4TZ0 (1, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split15A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split16A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split16A0X0Y0_check. -/
theorem Z0Split16A0X0Y0_check : checkGrid m4TZ0 2 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split16A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split16A0X0Y0_pairs. -/
theorem Z0Split16A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split16A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
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
      exact Z0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split16A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split16A0X0_pairs. -/
theorem Z0Split16A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split16A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split16A0_pairs. -/
theorem Z0Split16A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split16A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split16_check. -/
theorem Z0Split16_check : checkSplit m4TZ0 (2, 0, 2, 2) = true := by
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
    · exact Z0Split16A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split17A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0X0Y0_check. -/
theorem Z0Split17A0X0Y0_check : checkGrid m4TZ0 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split17A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0X0Y0_pairs. -/
theorem Z0Split17A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split17A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split17A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0X0_pairs. -/
theorem Z0Split17A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split17A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0_pairs. -/
theorem Z0Split17A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split17A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split17_check. -/
theorem Z0Split17_check : checkSplit m4TZ0 (2, 1, 1, 2) = true := by
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
    · exact Z0Split17A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split18A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0X0Y0_check. -/
theorem Z0Split18A0X0Y0_check : checkGrid m4TZ0 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split18A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0X0Y0_pairs. -/
theorem Z0Split18A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split18A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split18A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0X0_pairs. -/
theorem Z0Split18A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split18A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0_pairs. -/
theorem Z0Split18A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split18A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split18_check. -/
theorem Z0Split18_check : checkSplit m4TZ0 (2, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split18A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split19A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0X0Y0_check. -/
theorem Z0Split19A0X0Y0_check : checkGrid m4TZ0 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split19A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0X0Y0_pairs. -/
theorem Z0Split19A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split19A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split19A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0X0_pairs. -/
theorem Z0Split19A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split19A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0_pairs. -/
theorem Z0Split19A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split19A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split19_check. -/
theorem Z0Split19_check : checkSplit m4TZ0 (3, 0, 1, 2) = true := by
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
    · exact Z0Split19A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split20A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0X0Y0_check. -/
theorem Z0Split20A0X0Y0_check : checkGrid m4TZ0 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split20A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0X0Y0_pairs. -/
theorem Z0Split20A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split20A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split20A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0X0_pairs. -/
theorem Z0Split20A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split20A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0_pairs. -/
theorem Z0Split20A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split20A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split20_check. -/
theorem Z0Split20_check : checkSplit m4TZ0 (3, 1, 0, 2) = true := by
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
    · exact Z0Split20A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split21A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0X0Y0_check. -/
theorem Z0Split21A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split21A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0X0Y0_pairs. -/
theorem Z0Split21A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split21A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split21A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0X0_pairs. -/
theorem Z0Split21A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split21A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0_pairs. -/
theorem Z0Split21A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split21A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split21_check. -/
theorem Z0Split21_check : checkSplit m4TZ0 (4, 0, 0, 2) = true := by
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
    · exact Z0Split21A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0X0Y0_check. -/
theorem Z0Split22A0X0Y0_check : checkGrid m4TZ0 3 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0X0Y0_pairs. -/
theorem Z0Split22A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split22A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0X0_pairs. -/
theorem Z0Split22A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0_pairs. -/
theorem Z0Split22A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1X0Y0_check. -/
theorem Z0Split22A1X0Y0_check : checkGrid m4TZ0 3 376821623 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1X0Y0_pairs. -/
theorem Z0Split22A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split22A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1X0_pairs. -/
theorem Z0Split22A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1_pairs. -/
theorem Z0Split22A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2X0Y0_check. -/
theorem Z0Split22A2X0Y0_check : checkGrid m4TZ0 3 768556269 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2X0Y0_pairs. -/
theorem Z0Split22A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split22A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2X0_pairs. -/
theorem Z0Split22A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2_pairs. -/
theorem Z0Split22A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3X0Y0_check. -/
theorem Z0Split22A3X0Y0_check : checkGrid m4TZ0 3 1002105754 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3X0Y0_pairs. -/
theorem Z0Split22A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split22A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3X0_pairs. -/
theorem Z0Split22A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3_pairs. -/
theorem Z0Split22A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split22_check. -/
theorem Z0Split22_check : checkSplit m4TZ0 (0, 0, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split22A0_pairs x hx y hy hw
    · exact Z0Split22A1_pairs x hx y hy hw
    · exact Z0Split22A2_pairs x hx y hy hw
    · exact Z0Split22A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0X0Y0_check. -/
theorem Z0Split23A0X0Y0_check : checkGrid m4TZ0 3 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0X0Y0_pairs. -/
theorem Z0Split23A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split23A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0X0_pairs. -/
theorem Z0Split23A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0_pairs. -/
theorem Z0Split23A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1X0Y0_check. -/
theorem Z0Split23A1X0Y0_check : checkGrid m4TZ0 3 376821623 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1X0Y0_pairs. -/
theorem Z0Split23A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split23A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1X0_pairs. -/
theorem Z0Split23A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1_pairs. -/
theorem Z0Split23A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2X0Y0_check. -/
theorem Z0Split23A2X0Y0_check : checkGrid m4TZ0 3 768556269 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2X0Y0_pairs. -/
theorem Z0Split23A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split23A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2X0_pairs. -/
theorem Z0Split23A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2_pairs. -/
theorem Z0Split23A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3X0Y0_check. -/
theorem Z0Split23A3X0Y0_check : checkGrid m4TZ0 3 1002105754 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3X0Y0_pairs. -/
theorem Z0Split23A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split23A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3X0_pairs. -/
theorem Z0Split23A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3_pairs. -/
theorem Z0Split23A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split23_check. -/
theorem Z0Split23_check : checkSplit m4TZ0 (0, 1, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split23A0_pairs x hx y hy hw
    · exact Z0Split23A1_pairs x hx y hy hw
    · exact Z0Split23A2_pairs x hx y hy hw
    · exact Z0Split23A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A0X0Y0_check. -/
theorem Z0Split24A0X0Y0_check : checkGrid m4TZ0 3 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A0X0Y0_pairs. -/
theorem Z0Split24A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split24A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A0X0_pairs. -/
theorem Z0Split24A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A0_pairs. -/
theorem Z0Split24A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split24A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A1X0Y0_check. -/
theorem Z0Split24A1X0Y0_check : checkGrid m4TZ0 3 376821623 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A1X0Y0_pairs. -/
theorem Z0Split24A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split24A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A1X0_pairs. -/
theorem Z0Split24A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A1_pairs. -/
theorem Z0Split24A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split24A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A2X0Y0_check. -/
theorem Z0Split24A2X0Y0_check : checkGrid m4TZ0 3 768556269 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A2X0Y0_pairs. -/
theorem Z0Split24A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split24A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A2X0_pairs. -/
theorem Z0Split24A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A2_pairs. -/
theorem Z0Split24A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split24A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A3X0Y0_check. -/
theorem Z0Split24A3X0Y0_check : checkGrid m4TZ0 3 1002105754 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A3X0Y0_pairs. -/
theorem Z0Split24A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split24A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A3X0_pairs. -/
theorem Z0Split24A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A3_pairs. -/
theorem Z0Split24A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split24A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split24_check. -/
theorem Z0Split24_check : checkSplit m4TZ0 (0, 2, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split24A0_pairs x hx y hy hw
    · exact Z0Split24A1_pairs x hx y hy hw
    · exact Z0Split24A2_pairs x hx y hy hw
    · exact Z0Split24A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split25A0X0Y0Certs : List (Nat × Nat) := [
  (336, 356), (408, 395), (584, 500), (741, 577), (893, 669),
  (952, 708), (1099, 805), (1147, 846), (1259, 877), (1422, 973),
  (1443, 977), (1625, 1069), (1772, 1146), (1919, 1223), (2072, 1331),
  (2200, 1396), (2271, 1431), (2340, 1468), (2530, 1527), (2626, 1588),
  (2784, 1658), (2834, 1685), (2942, 1756), (3196, 1890), (3308, 1957),
  (3390, 1986), (3577, 2052), (3711, 2134), (3726, 2143), (4005, 2297)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0Y0_check. -/
theorem Z0Split25A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split25A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0Y0_pairs. -/
theorem Z0Split25A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split25A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split25A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0_pairs. -/
theorem Z0Split25A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split25A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0_pairs. -/
theorem Z0Split25A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split25A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split25_check. -/
theorem Z0Split25_check : checkSplit m4TZ0 (0, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split25A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split26A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split26A0X0Y0_check. -/
theorem Z0Split26A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split26A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split26A0X0Y0_pairs. -/
theorem Z0Split26A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split26A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split26A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split26A0X0_pairs. -/
theorem Z0Split26A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split26A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split26A0_pairs. -/
theorem Z0Split26A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split26A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split26_check. -/
theorem Z0Split26_check : checkSplit m4TZ0 (0, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split26A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split27A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0X0Y0_check. -/
theorem Z0Split27A0X0Y0_check : checkGrid m4TZ0 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split27A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0X0Y0_pairs. -/
theorem Z0Split27A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split27A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split27A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0X0_pairs. -/
theorem Z0Split27A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split27A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0_pairs. -/
theorem Z0Split27A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split27A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split27_check. -/
theorem Z0Split27_check : checkSplit m4TZ0 (0, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split27A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split28A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0X0Y0_check. -/
theorem Z0Split28A0X0Y0_check : checkGrid m4TZ0 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split28A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0X0Y0_pairs. -/
theorem Z0Split28A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split28A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split28A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0X0_pairs. -/
theorem Z0Split28A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split28A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0_pairs. -/
theorem Z0Split28A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split28A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split28_check. -/
theorem Z0Split28_check : checkSplit m4TZ0 (0, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split28A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0X0Y0_check. -/
theorem Z0Split29A0X0Y0_check : checkGrid m4TZ0 3 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0X0Y0_pairs. -/
theorem Z0Split29A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split29A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0X0_pairs. -/
theorem Z0Split29A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0_pairs. -/
theorem Z0Split29A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1X0Y0_check. -/
theorem Z0Split29A1X0Y0_check : checkGrid m4TZ0 3 376821623 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1X0Y0_pairs. -/
theorem Z0Split29A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split29A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1X0_pairs. -/
theorem Z0Split29A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1_pairs. -/
theorem Z0Split29A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2X0Y0_check. -/
theorem Z0Split29A2X0Y0_check : checkGrid m4TZ0 3 768556269 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2X0Y0_pairs. -/
theorem Z0Split29A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split29A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2X0_pairs. -/
theorem Z0Split29A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2_pairs. -/
theorem Z0Split29A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3X0Y0_check. -/
theorem Z0Split29A3X0Y0_check : checkGrid m4TZ0 3 1002105754 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3X0Y0_pairs. -/
theorem Z0Split29A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split29A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3X0_pairs. -/
theorem Z0Split29A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3_pairs. -/
theorem Z0Split29A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split29_check. -/
theorem Z0Split29_check : checkSplit m4TZ0 (1, 0, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split29A0_pairs x hx y hy hw
    · exact Z0Split29A1_pairs x hx y hy hw
    · exact Z0Split29A2_pairs x hx y hy hw
    · exact Z0Split29A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A0X0Y0Certs : List (Nat × Nat) := [
  (283, 992), (469, 1191), (654, 1844)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0X0Y0_check. -/
theorem Z0Split30A0X0Y0_check : checkGrid m4TZ0 3 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0X0Y0_pairs. -/
theorem Z0Split30A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split30A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0X0_pairs. -/
theorem Z0Split30A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0_pairs. -/
theorem Z0Split30A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A1X0Y0Certs : List (Nat × Nat) := [
  (127, 1987)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1X0Y0_check. -/
theorem Z0Split30A1X0Y0_check : checkGrid m4TZ0 3 376821623 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1X0Y0_pairs. -/
theorem Z0Split30A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split30A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1X0_pairs. -/
theorem Z0Split30A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1_pairs. -/
theorem Z0Split30A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A2X0Y0Certs : List (Nat × Nat) := [
  (33, 2279)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2X0Y0_check. -/
theorem Z0Split30A2X0Y0_check : checkGrid m4TZ0 3 768556269 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2X0Y0_pairs. -/
theorem Z0Split30A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split30A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2X0_pairs. -/
theorem Z0Split30A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2_pairs. -/
theorem Z0Split30A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3X0Y0_check. -/
theorem Z0Split30A3X0Y0_check : checkGrid m4TZ0 3 1002105754 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3X0Y0_pairs. -/
theorem Z0Split30A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split30A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3X0_pairs. -/
theorem Z0Split30A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3_pairs. -/
theorem Z0Split30A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split30_check. -/
theorem Z0Split30_check : checkSplit m4TZ0 (1, 1, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split30A0_pairs x hx y hy hw
    · exact Z0Split30A1_pairs x hx y hy hw
    · exact Z0Split30A2_pairs x hx y hy hw
    · exact Z0Split30A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A0X0Y0Certs : List (Nat × Nat) := [
  (1800, 0), (2008, 252), (3042, 0), (4287, 604), (4795, 1225),
  (6932, 1271), (7442, 1892), (9194, 1830), (10495, 0), (12958, 578)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A0X0Y0_check. -/
theorem Z0Split31A0X0Y0_check : checkGrid m4TZ0 3 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A0X0Y0_pairs. -/
theorem Z0Split31A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split31A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A0X0_pairs. -/
theorem Z0Split31A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A0_pairs. -/
theorem Z0Split31A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split31A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A1X0Y0_check. -/
theorem Z0Split31A1X0Y0_check : checkGrid m4TZ0 3 376821623 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A1X0Y0_pairs. -/
theorem Z0Split31A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split31A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A1X0_pairs. -/
theorem Z0Split31A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A1_pairs. -/
theorem Z0Split31A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split31A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A2X0Y0Certs : List (Nat × Nat) := [
  (580, 2253), (2006, 0), (10131, 2298), (11988, 2135)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A2X0Y0_check. -/
theorem Z0Split31A2X0Y0_check : checkGrid m4TZ0 3 768556269 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A2X0Y0_pairs. -/
theorem Z0Split31A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split31A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A2X0_pairs. -/
theorem Z0Split31A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A2_pairs. -/
theorem Z0Split31A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split31A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A3X0Y0_check. -/
theorem Z0Split31A3X0Y0_check : checkGrid m4TZ0 3 1002105754 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A3X0Y0_pairs. -/
theorem Z0Split31A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split31A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A3X0_pairs. -/
theorem Z0Split31A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A3_pairs. -/
theorem Z0Split31A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split31A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split31_check. -/
theorem Z0Split31_check : checkSplit m4TZ0 (1, 2, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split31A0_pairs x hx y hy hw
    · exact Z0Split31A1_pairs x hx y hy hw
    · exact Z0Split31A2_pairs x hx y hy hw
    · exact Z0Split31A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split32A0X0Y0Certs : List (Nat × Nat) := [
  (4902, 464), (7623, 997), (10005, 22), (11753, 67), (12657, 186)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split32A0X0Y0_check. -/
theorem Z0Split32A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split32A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split32A0X0Y0_pairs. -/
theorem Z0Split32A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split32A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split32A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split32A0X0_pairs. -/
theorem Z0Split32A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split32A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split32A0_pairs. -/
theorem Z0Split32A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split32A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split32_check. -/
theorem Z0Split32_check : checkSplit m4TZ0 (1, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split32A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split33A0X0Y0Certs : List (Nat × Nat) := [
  (59, 2092), (131, 231), (287, 535), (473, 1131), (657, 1731)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0X0Y0_check. -/
theorem Z0Split33A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split33A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0X0Y0_pairs. -/
theorem Z0Split33A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split33A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split33A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0X0_pairs. -/
theorem Z0Split33A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split33A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0_pairs. -/
theorem Z0Split33A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split33A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split33_check. -/
theorem Z0Split33_check : checkSplit m4TZ0 (1, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split33A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split34A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0X0Y0_check. -/
theorem Z0Split34A0X0Y0_check : checkGrid m4TZ0 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split34A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0X0Y0_pairs. -/
theorem Z0Split34A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split34A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split34A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0X0_pairs. -/
theorem Z0Split34A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split34A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0_pairs. -/
theorem Z0Split34A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split34A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split34_check. -/
theorem Z0Split34_check : checkSplit m4TZ0 (1, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split34A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0X0Y0_check. -/
theorem Z0Split35A0X0Y0_check : checkGrid m4TZ0 3 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0X0Y0_pairs. -/
theorem Z0Split35A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0X0_pairs. -/
theorem Z0Split35A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0_pairs. -/
theorem Z0Split35A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1X0Y0_check. -/
theorem Z0Split35A1X0Y0_check : checkGrid m4TZ0 3 376821623 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1X0Y0_pairs. -/
theorem Z0Split35A1X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1X0_pairs. -/
theorem Z0Split35A1X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1_pairs. -/
theorem Z0Split35A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2X0Y0_check. -/
theorem Z0Split35A2X0Y0_check : checkGrid m4TZ0 3 768556269 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2X0Y0_pairs. -/
theorem Z0Split35A2X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2X0_pairs. -/
theorem Z0Split35A2X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2_pairs. -/
theorem Z0Split35A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3X0Y0_check. -/
theorem Z0Split35A3X0Y0_check : checkGrid m4TZ0 3 1002105754 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3X0Y0_pairs. -/
theorem Z0Split35A3X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3X0_pairs. -/
theorem Z0Split35A3X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3_pairs. -/
theorem Z0Split35A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split35_check. -/
theorem Z0Split35_check : checkSplit m4TZ0 (2, 0, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split35A0_pairs x hx y hy hw
    · exact Z0Split35A1_pairs x hx y hy hw
    · exact Z0Split35A2_pairs x hx y hy hw
    · exact Z0Split35A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A0X0Y0Certs : List (Nat × Nat) := [
  (3030, 0), (3492, 463), (3998, 0), (6828, 996), (7363, 194),
  (7620, 1229), (9174, 1015), (10369, 475), (10652, 1748), (11643, 1548),
  (11698, 0), (11912, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0X0Y0_check. -/
theorem Z0Split36A0X0Y0_check : checkGrid m4TZ0 3 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0X0Y0_pairs. -/
theorem Z0Split36A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0X0_pairs. -/
theorem Z0Split36A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0_pairs. -/
theorem Z0Split36A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A1X0Y0Certs : List (Nat × Nat) := [
  (3847, 1945)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1X0Y0_check. -/
theorem Z0Split36A1X0Y0_check : checkGrid m4TZ0 3 376821623 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1X0Y0_pairs. -/
theorem Z0Split36A1X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1X0_pairs. -/
theorem Z0Split36A1X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1_pairs. -/
theorem Z0Split36A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A2X0Y0Certs : List (Nat × Nat) := [
  (12456, 2125)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2X0Y0_check. -/
theorem Z0Split36A2X0Y0_check : checkGrid m4TZ0 3 768556269 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2X0Y0_pairs. -/
theorem Z0Split36A2X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2X0_pairs. -/
theorem Z0Split36A2X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2_pairs. -/
theorem Z0Split36A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3X0Y0_check. -/
theorem Z0Split36A3X0Y0_check : checkGrid m4TZ0 3 1002105754 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3X0Y0_pairs. -/
theorem Z0Split36A3X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3X0_pairs. -/
theorem Z0Split36A3X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3_pairs. -/
theorem Z0Split36A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split36_check. -/
theorem Z0Split36_check : checkSplit m4TZ0 (2, 1, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split36A0_pairs x hx y hy hw
    · exact Z0Split36A1_pairs x hx y hy hw
    · exact Z0Split36A2_pairs x hx y hy hw
    · exact Z0Split36A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split37A0X0Y0Certs : List (Nat × Nat) := [
  (12681, 273), (41480, 632), (86580, 96)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X0Y0_check. -/
theorem Z0Split37A0X0Y0_check : checkGrid m4TZ0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X0Y0_pairs. -/
theorem Z0Split37A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split37A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X0_pairs. -/
theorem Z0Split37A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split37A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split37A0X1Y0Certs : List (Nat × Nat) := [
  (25733, 276), (62364, 644)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X1Y0_check. -/
theorem Z0Split37A0X1Y0_check : checkGrid m4TZ0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X1Y0_pairs. -/
theorem Z0Split37A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split37A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X1_pairs. -/
theorem Z0Split37A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split37A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0_pairs. -/
theorem Z0Split37A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split37A0X0_pairs x hx y hy hw
  · exact Z0Split37A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split37_check. -/
theorem Z0Split37_check : checkSplit m4TZ0 (2, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split37A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split38A0X0Y0Certs : List (Nat × Nat) := [
  (978, 616), (3000, 1), (3934, 58), (6152, 25), (7449, 167),
  (9636, 88), (10455, 415), (10701, 906), (11382, 267), (12481, 14)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0X0Y0_check. -/
theorem Z0Split38A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split38A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0X0Y0_pairs. -/
theorem Z0Split38A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split38A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split38A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0X0_pairs. -/
theorem Z0Split38A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split38A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0_pairs. -/
theorem Z0Split38A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split38A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split38_check. -/
theorem Z0Split38_check : checkSplit m4TZ0 (2, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split38A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split39A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0X0Y0_check. -/
theorem Z0Split39A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split39A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0X0Y0_pairs. -/
theorem Z0Split39A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split39A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split39A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0X0_pairs. -/
theorem Z0Split39A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split39A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0_pairs. -/
theorem Z0Split39A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split39A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split39_check. -/
theorem Z0Split39_check : checkSplit m4TZ0 (2, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split39A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split40A0X0Y0Certs : List (Nat × Nat) := [
  (250, 286), (514, 461), (897, 673), (913, 680), (987, 754),
  (990, 759), (1206, 866), (1455, 980), (1475, 993), (1581, 1052),
  (1586, 1057), (1877, 1195), (2097, 1346), (2104, 1353), (2222, 1406),
  (2386, 1487), (2394, 1490), (2455, 1506), (2715, 1623), (2724, 1630),
  (2864, 1699), (3056, 1805), (3066, 1811), (3139, 1851), (3291, 1949),
  (3461, 2017), (3473, 2020), (3691, 2124), (3902, 2235), (3917, 2243)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0Y0_check. -/
theorem Z0Split40A0X0Y0_check : checkGrid m4TZ0 2 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split40A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0Y0_pairs. -/
theorem Z0Split40A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split40A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
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
      exact Z0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split40A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0_pairs. -/
theorem Z0Split40A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split40A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0_pairs. -/
theorem Z0Split40A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split40A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split40_check. -/
theorem Z0Split40_check : checkSplit m4TZ0 (3, 0, 3, 2) = true := by
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
    · exact Z0Split40A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split41A0X0Y0Certs : List (Nat × Nat) := [
  (520, 342), (1924, 784), (4210, 1392), (6804, 1300), (9159, 124)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split41A0X0Y0_check. -/
theorem Z0Split41A0X0Y0_check : checkGrid m4TZ0 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split41A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split41A0X0Y0_pairs. -/
theorem Z0Split41A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split41A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
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
      exact Z0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split41A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split41A0X0_pairs. -/
theorem Z0Split41A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split41A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split41A0_pairs. -/
theorem Z0Split41A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split41A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split41_check. -/
theorem Z0Split41_check : checkSplit m4TZ0 (3, 1, 2, 2) = true := by
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
    · exact Z0Split41A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split42A0X0Y0Certs : List (Nat × Nat) := [
  (1066, 476), (3142, 1017), (6296, 1561), (9725, 74), (11440, 199)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0X0Y0_check. -/
theorem Z0Split42A0X0Y0_check : checkGrid m4TZ0 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split42A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0X0Y0_pairs. -/
theorem Z0Split42A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split42A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split42A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0X0_pairs. -/
theorem Z0Split42A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split42A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0_pairs. -/
theorem Z0Split42A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split42A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split42_check. -/
theorem Z0Split42_check : checkSplit m4TZ0 (3, 2, 1, 2) = true := by
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
    · exact Z0Split42A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split43A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X0Y0_check. -/
theorem Z0Split43A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split43A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X0Y0_pairs. -/
theorem Z0Split43A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split43A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split43A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X0_pairs. -/
theorem Z0Split43A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split43A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0_pairs. -/
theorem Z0Split43A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split43A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split43_check. -/
theorem Z0Split43_check : checkSplit m4TZ0 (3, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split43A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split44A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split44A0X0Y0_check. -/
theorem Z0Split44A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split44A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split44A0X0Y0_pairs. -/
theorem Z0Split44A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split44A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
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
      exact Z0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split44A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split44A0X0_pairs. -/
theorem Z0Split44A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split44A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split44A0_pairs. -/
theorem Z0Split44A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split44A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split44_check. -/
theorem Z0Split44_check : checkSplit m4TZ0 (4, 0, 2, 2) = true := by
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
    · exact Z0Split44A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split45A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0X0Y0_check. -/
theorem Z0Split45A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split45A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0X0Y0_pairs. -/
theorem Z0Split45A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split45A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split45A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0X0_pairs. -/
theorem Z0Split45A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split45A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0_pairs. -/
theorem Z0Split45A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split45A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split45_check. -/
theorem Z0Split45_check : checkSplit m4TZ0 (4, 1, 1, 2) = true := by
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
    · exact Z0Split45A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split46A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0X0Y0_check. -/
theorem Z0Split46A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split46A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0X0Y0_pairs. -/
theorem Z0Split46A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split46A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split46A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0X0_pairs. -/
theorem Z0Split46A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split46A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0_pairs. -/
theorem Z0Split46A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split46A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split46_check. -/
theorem Z0Split46_check : checkSplit m4TZ0 (4, 2, 0, 2) = true := by
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
    · exact Z0Split46A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split47A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0X0Y0_check. -/
theorem Z0Split47A0X0Y0_check : checkGrid m4TZ0 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split47A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0X0Y0_pairs. -/
theorem Z0Split47A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split47A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split47A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0X0_pairs. -/
theorem Z0Split47A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split47A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0_pairs. -/
theorem Z0Split47A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split47A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split47_check. -/
theorem Z0Split47_check : checkSplit m4TZ0 (5, 0, 1, 2) = true := by
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
    · exact Z0Split47A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split48A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0X0Y0_check. -/
theorem Z0Split48A0X0Y0_check : checkGrid m4TZ0 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split48A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0X0Y0_pairs. -/
theorem Z0Split48A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split48A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split48A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0X0_pairs. -/
theorem Z0Split48A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split48A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0_pairs. -/
theorem Z0Split48A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split48A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split48_check. -/
theorem Z0Split48_check : checkSplit m4TZ0 (5, 1, 0, 2) = true := by
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
    · exact Z0Split48A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split49A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0X0Y0_check. -/
theorem Z0Split49A0X0Y0_check : checkGrid m4TZ0 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split49A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0X0Y0_pairs. -/
theorem Z0Split49A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split49A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split49A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0X0_pairs. -/
theorem Z0Split49A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split49A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0_pairs. -/
theorem Z0Split49A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split49A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split49_check. -/
theorem Z0Split49_check : checkSplit m4TZ0 (6, 0, 0, 2) = true := by
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
    · exact Z0Split49A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0X0Y0_check. -/
theorem Z0Split50A0X0Y0_check : checkGrid m4TZ0 3 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0X0Y0_pairs. -/
theorem Z0Split50A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 8 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split50A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0X0_pairs. -/
theorem Z0Split50A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 8 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0_pairs. -/
theorem Z0Split50A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 8 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1X0Y0_check. -/
theorem Z0Split50A1X0Y0_check : checkGrid m4TZ0 3 376821623 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1X0Y0_pairs. -/
theorem Z0Split50A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 8 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split50A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1X0_pairs. -/
theorem Z0Split50A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 8 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1_pairs. -/
theorem Z0Split50A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 8 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2X0Y0_check. -/
theorem Z0Split50A2X0Y0_check : checkGrid m4TZ0 3 768556269 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2X0Y0_pairs. -/
theorem Z0Split50A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 8 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split50A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2X0_pairs. -/
theorem Z0Split50A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 8 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2_pairs. -/
theorem Z0Split50A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 8 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3X0Y0_check. -/
theorem Z0Split50A3X0Y0_check : checkGrid m4TZ0 3 1002105754 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3X0Y0_pairs. -/
theorem Z0Split50A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 8 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split50A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3X0_pairs. -/
theorem Z0Split50A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 8 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3_pairs. -/
theorem Z0Split50A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 8 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split50_check. -/
theorem Z0Split50_check : checkSplit m4TZ0 (0, 0, 8, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split50A0_pairs x hx y hy hw
    · exact Z0Split50A1_pairs x hx y hy hw
    · exact Z0Split50A2_pairs x hx y hy hw
    · exact Z0Split50A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0X0Y0_check. -/
theorem Z0Split51A0X0Y0_check : checkGrid m4TZ0 3 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0X0Y0_pairs. -/
theorem Z0Split51A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split51A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0X0_pairs. -/
theorem Z0Split51A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0_pairs. -/
theorem Z0Split51A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1X0Y0_check. -/
theorem Z0Split51A1X0Y0_check : checkGrid m4TZ0 3 376821623 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1X0Y0_pairs. -/
theorem Z0Split51A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split51A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1X0_pairs. -/
theorem Z0Split51A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1_pairs. -/
theorem Z0Split51A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2X0Y0_check. -/
theorem Z0Split51A2X0Y0_check : checkGrid m4TZ0 3 768556269 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2X0Y0_pairs. -/
theorem Z0Split51A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split51A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2X0_pairs. -/
theorem Z0Split51A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2_pairs. -/
theorem Z0Split51A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3X0Y0_check. -/
theorem Z0Split51A3X0Y0_check : checkGrid m4TZ0 3 1002105754 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3X0Y0_pairs. -/
theorem Z0Split51A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split51A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3X0_pairs. -/
theorem Z0Split51A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3_pairs. -/
theorem Z0Split51A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split51_check. -/
theorem Z0Split51_check : checkSplit m4TZ0 (0, 1, 7, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split51A0_pairs x hx y hy hw
    · exact Z0Split51A1_pairs x hx y hy hw
    · exact Z0Split51A2_pairs x hx y hy hw
    · exact Z0Split51A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A0X0Y0Certs : List (Nat × Nat) := [
  (39, 0), (83, 1435), (176, 1868), (181, 1669), (238, 1383),
  (246, 0), (292, 1496), (332, 1665), (338, 1206)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A0X0Y0_check. -/
theorem Z0Split52A0X0Y0_check : checkGrid m4TZ0 3 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A0X0Y0_pairs. -/
theorem Z0Split52A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split52A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A0X0_pairs. -/
theorem Z0Split52A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A0_pairs. -/
theorem Z0Split52A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split52A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A1X0Y0Certs : List (Nat × Nat) := [
  (123, 2066), (129, 0), (234, 2028)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A1X0Y0_check. -/
theorem Z0Split52A1X0Y0_check : checkGrid m4TZ0 3 376821623 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A1X0Y0_pairs. -/
theorem Z0Split52A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split52A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A1X0_pairs. -/
theorem Z0Split52A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A1_pairs. -/
theorem Z0Split52A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split52A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A2X0Y0Certs : List (Nat × Nat) := [
  (118, 0), (286, 2282)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A2X0Y0_check. -/
theorem Z0Split52A2X0Y0_check : checkGrid m4TZ0 3 768556269 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A2X0Y0_pairs. -/
theorem Z0Split52A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split52A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A2X0_pairs. -/
theorem Z0Split52A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A2_pairs. -/
theorem Z0Split52A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split52A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A3X0Y0_check. -/
theorem Z0Split52A3X0Y0_check : checkGrid m4TZ0 3 1002105754 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A3X0Y0_pairs. -/
theorem Z0Split52A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split52A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A3X0_pairs. -/
theorem Z0Split52A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A3_pairs. -/
theorem Z0Split52A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split52A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split52_check. -/
theorem Z0Split52_check : checkSplit m4TZ0 (0, 2, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split52A0_pairs x hx y hy hw
    · exact Z0Split52A1_pairs x hx y hy hw
    · exact Z0Split52A2_pairs x hx y hy hw
    · exact Z0Split52A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A0X0Y0Certs : List (Nat × Nat) := [
  (911, 0), (2579, 0), (2851, 0), (3351, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0Y0_check. -/
theorem Z0Split53A0X0Y0_check : checkGrid m4TZ0 3 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0Y0_pairs. -/
theorem Z0Split53A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split53A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0_pairs. -/
theorem Z0Split53A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split53A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0_pairs. -/
theorem Z0Split53A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split53A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A1X0Y0Certs : List (Nat × Nat) := [
  (191, 0), (2363, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0Y0_check. -/
theorem Z0Split53A1X0Y0_check : checkGrid m4TZ0 3 376821623 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0Y0_pairs. -/
theorem Z0Split53A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split53A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0_pairs. -/
theorem Z0Split53A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split53A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1_pairs. -/
theorem Z0Split53A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split53A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A2X0Y0Certs : List (Nat × Nat) := [
  (1287, 0), (1839, 0), (2406, 0), (3765, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0Y0_check. -/
theorem Z0Split53A2X0Y0_check : checkGrid m4TZ0 3 768556269 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0Y0_pairs. -/
theorem Z0Split53A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split53A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0_pairs. -/
theorem Z0Split53A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split53A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2_pairs. -/
theorem Z0Split53A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split53A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0Y0_check. -/
theorem Z0Split53A3X0Y0_check : checkGrid m4TZ0 3 1002105754 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0Y0_pairs. -/
theorem Z0Split53A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split53A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0_pairs. -/
theorem Z0Split53A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split53A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3_pairs. -/
theorem Z0Split53A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split53A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split53_check. -/
theorem Z0Split53_check : checkSplit m4TZ0 (0, 3, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split53A0_pairs x hx y hy hw
    · exact Z0Split53A1_pairs x hx y hy hw
    · exact Z0Split53A2_pairs x hx y hy hw
    · exact Z0Split53A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y0Certs : List (Nat × Nat) := [
  (677, 307), (3812, 719), (4020, 775), (7461, 1058), (8365, 1108),
  (8409, 1111), (9737, 1240), (9818, 1246), (10925, 1354), (11271, 1374),
  (15523, 1631), (15598, 1634), (17152, 1712), (17215, 1715), (18367, 1819),
  (19457, 1888), (23772, 2112), (24508, 2178), (26737, 2303), (26931, 2310)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y0_check. -/
theorem Z0Split54A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y0_pairs. -/
theorem Z0Split54A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · exact Z0Split54A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0_pairs. -/
theorem Z0Split54A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split54A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0_pairs. -/
theorem Z0Split54A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split54A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split54_check. -/
theorem Z0Split54_check : checkSplit m4TZ0 (0, 4, 4, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split54A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split55A0X0Y0Certs : List (Nat × Nat) := [
  (180, 242), (443, 410), (592, 506), (748, 582), (1315, 897),
  (1365, 932), (1640, 1079), (1826, 1174), (1930, 1232), (2515, 1522),
  (2585, 1552), (2805, 1672), (2991, 1773), (3002, 1776), (3063, 1810),
  (3322, 1963), (3384, 1985), (3809, 2181), (3824, 2188), (3913, 2242)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0Y0_check. -/
theorem Z0Split55A0X0Y0_check : checkGrid m4TZ0 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split55A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0Y0_pairs. -/
theorem Z0Split55A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split55A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split55A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0_pairs. -/
theorem Z0Split55A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split55A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0_pairs. -/
theorem Z0Split55A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split55A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split55_check. -/
theorem Z0Split55_check : checkSplit m4TZ0 (0, 5, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split55A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split56A0X0Y0Certs : List (Nat × Nat) := [
  (39, 182), (112, 446), (172, 737), (195, 849), (223, 962),
  (239, 1042), (280, 1303), (310, 1471), (339, 1610), (394, 1990)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split56A0X0Y0_check. -/
theorem Z0Split56A0X0Y0_check : checkGrid m4TZ0 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split56A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split56A0X0Y0_pairs. -/
theorem Z0Split56A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split56A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split56A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split56A0X0_pairs. -/
theorem Z0Split56A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split56A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split56A0_pairs. -/
theorem Z0Split56A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split56A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split56_check. -/
theorem Z0Split56_check : checkSplit m4TZ0 (0, 6, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split56A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split57A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0X0Y0_check. -/
theorem Z0Split57A0X0Y0_check : checkGrid m4TZ0 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split57A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0X0Y0_pairs. -/
theorem Z0Split57A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split57A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split57A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0X0_pairs. -/
theorem Z0Split57A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split57A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0_pairs. -/
theorem Z0Split57A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split57A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split57_check. -/
theorem Z0Split57_check : checkSplit m4TZ0 (0, 7, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split57A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split58A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0X0Y0_check. -/
theorem Z0Split58A0X0Y0_check : checkGrid m4TZ0 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split58A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0X0Y0_pairs. -/
theorem Z0Split58A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 8 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split58A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split58A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0X0_pairs. -/
theorem Z0Split58A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 8 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split58A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0_pairs. -/
theorem Z0Split58A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 8 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split58A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split58_check. -/
theorem Z0Split58_check : checkSplit m4TZ0 (0, 8, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split58A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0X0Y0_check. -/
theorem Z0Split59A0X0Y0_check : checkGrid m4TZ0 3 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0X0Y0_pairs. -/
theorem Z0Split59A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split59A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0X0_pairs. -/
theorem Z0Split59A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0_pairs. -/
theorem Z0Split59A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1X0Y0_check. -/
theorem Z0Split59A1X0Y0_check : checkGrid m4TZ0 3 376821623 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1X0Y0_pairs. -/
theorem Z0Split59A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split59A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1X0_pairs. -/
theorem Z0Split59A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1_pairs. -/
theorem Z0Split59A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2X0Y0_check. -/
theorem Z0Split59A2X0Y0_check : checkGrid m4TZ0 3 768556269 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2X0Y0_pairs. -/
theorem Z0Split59A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split59A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2X0_pairs. -/
theorem Z0Split59A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2_pairs. -/
theorem Z0Split59A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3X0Y0_check. -/
theorem Z0Split59A3X0Y0_check : checkGrid m4TZ0 3 1002105754 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3X0Y0_pairs. -/
theorem Z0Split59A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split59A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3X0_pairs. -/
theorem Z0Split59A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3_pairs. -/
theorem Z0Split59A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split59_check. -/
theorem Z0Split59_check : checkSplit m4TZ0 (1, 0, 7, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split59A0_pairs x hx y hy hw
    · exact Z0Split59A1_pairs x hx y hy hw
    · exact Z0Split59A2_pairs x hx y hy hw
    · exact Z0Split59A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A0X0Y0Certs : List (Nat × Nat) := [
  (21, 0), (120, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0X0Y0_check. -/
theorem Z0Split60A0X0Y0_check : checkGrid m4TZ0 3 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0X0Y0_pairs. -/
theorem Z0Split60A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split60A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0X0_pairs. -/
theorem Z0Split60A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0_pairs. -/
theorem Z0Split60A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1X0Y0_check. -/
theorem Z0Split60A1X0Y0_check : checkGrid m4TZ0 3 376821623 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1X0Y0_pairs. -/
theorem Z0Split60A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split60A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1X0_pairs. -/
theorem Z0Split60A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1_pairs. -/
theorem Z0Split60A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2X0Y0_check. -/
theorem Z0Split60A2X0Y0_check : checkGrid m4TZ0 3 768556269 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2X0Y0_pairs. -/
theorem Z0Split60A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split60A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2X0_pairs. -/
theorem Z0Split60A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2_pairs. -/
theorem Z0Split60A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3X0Y0_check. -/
theorem Z0Split60A3X0Y0_check : checkGrid m4TZ0 3 1002105754 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3X0Y0_pairs. -/
theorem Z0Split60A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split60A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3X0_pairs. -/
theorem Z0Split60A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3_pairs. -/
theorem Z0Split60A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split60_check. -/
theorem Z0Split60_check : checkSplit m4TZ0 (1, 1, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split60A0_pairs x hx y hy hw
    · exact Z0Split60A1_pairs x hx y hy hw
    · exact Z0Split60A2_pairs x hx y hy hw
    · exact Z0Split60A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split61A0X0Y0Certs : List (Nat × Nat) := [
  (490, 1801), (826, 0), (1154, 0), (1361, 0), (1720, 0),
  (2206, 1199), (2569, 1845), (3441, 0), (3637, 0), (3914, 0),
  (4007, 1128), (4174, 1674), (4448, 1861), (4532, 311), (6098, 0),
  (6140, 0), (6266, 0), (6422, 0), (6719, 1708), (6888, 1525),
  (7253, 725), (7645, 0), (8979, 0), (9444, 1899), (9712, 0),
  (9765, 1690), (9826, 1270), (9889, 1399), (9994, 0), (10795, 0),
  (11620, 1701), (11668, 1826), (11712, 1391), (11946, 0), (12621, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A0X0Y0_check. -/
theorem Z0Split61A0X0Y0_check : checkGrid m4TZ0 3 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A0X0Y0_pairs. -/
theorem Z0Split61A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split61A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A0X0_pairs. -/
theorem Z0Split61A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A0_pairs. -/
theorem Z0Split61A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split61A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split61A1X0Y0Certs : List (Nat × Nat) := [
  (1958, 1999), (4173, 0), (7299, 2029), (9559, 2037)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A1X0Y0_check. -/
theorem Z0Split61A1X0Y0_check : checkGrid m4TZ0 3 376821623 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A1X0Y0_pairs. -/
theorem Z0Split61A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split61A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A1X0_pairs. -/
theorem Z0Split61A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A1_pairs. -/
theorem Z0Split61A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split61A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split61A2X0Y0Certs : List (Nat × Nat) := [
  (828, 2266), (1402, 0), (1878, 2231), (2594, 2211), (4589, 2280),
  (6420, 0), (7163, 2198), (9988, 0), (10005, 0), (11703, 0),
  (11833, 0), (12137, 0), (12279, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A2X0Y0_check. -/
theorem Z0Split61A2X0Y0_check : checkGrid m4TZ0 3 768556269 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A2X0Y0_pairs. -/
theorem Z0Split61A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split61A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A2X0_pairs. -/
theorem Z0Split61A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A2_pairs. -/
theorem Z0Split61A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split61A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split61A3X0Y0Certs : List (Nat × Nat) := [
  (587, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A3X0Y0_check. -/
theorem Z0Split61A3X0Y0_check : checkGrid m4TZ0 3 1002105754 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A3X0Y0_pairs. -/
theorem Z0Split61A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split61A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A3X0_pairs. -/
theorem Z0Split61A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A3_pairs. -/
theorem Z0Split61A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split61A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split61_check. -/
theorem Z0Split61_check : checkSplit m4TZ0 (1, 2, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split61A0_pairs x hx y hy hw
    · exact Z0Split61A1_pairs x hx y hy hw
    · exact Z0Split61A2_pairs x hx y hy hw
    · exact Z0Split61A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y0Certs : List (Nat × Nat) := [
  (19703, 668), (20036, 703), (21421, 366), (21885, 448), (39912, 612),
  (40400, 691), (44106, 653), (48907, 724), (57928, 293), (62929, 455),
  (66927, 443), (69110, 697), (85462, 692), (89914, 753), (90786, 305),
  (92572, 565), (109607, 647), (110027, 687), (110290, 713), (111271, 308),
  (119482, 310), (121591, 601), (122599, 720)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y0_check. -/
theorem Z0Split62A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y0_pairs. -/
theorem Z0Split62A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S4096Chunk0_bound y hy)
  · exact Z0Split62A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y1Certs : List (Nat × Nat) := [
  (751, 843), (7638, 1072), (22595, 950), (36606, 1091), (40483, 1080),
  (41594, 820), (43162, 967), (44262, 1047), (49822, 821), (63616, 965),
  (65669, 789), (66234, 822), (88490, 982), (91988, 902), (92226, 949),
  (92259, 956), (92717, 994), (94044, 1095), (104641, 969), (115286, 815)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y1_check. -/
theorem Z0Split62A0X0Y1_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk1
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y1_pairs. -/
theorem Z0Split62A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S4096Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk1
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S4096Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S4096Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S4096Chunk1_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S4096Chunk1_bound y hy)
  · exact Z0Split62A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y2Certs : List (Nat × Nat) := [
  (1212, 1204), (6769, 1345), (13033, 1160), (14544, 1280), (17213, 1175),
  (19037, 1343), (21808, 1213), (35228, 1313), (40669, 1416), (46235, 1201),
  (46640, 1244), (47009, 1263), (62844, 1222), (63483, 1268), (63860, 1283),
  (68440, 1362), (71691, 1269), (76886, 1382), (77069, 1390), (93672, 1402),
  (93822, 1409), (98711, 1119), (107608, 1192), (107616, 1196), (109017, 1325),
  (111843, 1210), (120362, 1242)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y2_check. -/
theorem Z0Split62A0X0Y2_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk2
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y2_pairs. -/
theorem Z0Split62A0X0Y2_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S4096Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk2
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S4096Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S4096Chunk2
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S4096Chunk2_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S4096Chunk2_bound y hy)
  · exact Z0Split62A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y3Certs : List (Nat × Nat) := [
  (8606, 1465), (20124, 1661), (40316, 1640), (65349, 1673), (68652, 1617),
  (70274, 1483), (80452, 1556), (87728, 1523), (108634, 1534), (108927, 1553)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y3_check. -/
theorem Z0Split62A0X0Y3_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk3
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y3_pairs. -/
theorem Z0Split62A0X0Y3_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S4096Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk3
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S4096Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S4096Chunk3
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S4096Chunk3_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S4096Chunk3_bound y hy)
  · exact Z0Split62A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y4Certs : List (Nat × Nat) := [
  (10885, 1866), (13421, 1727), (16554, 1686), (22911, 1840), (22970, 1846),
  (22995, 1853), (30290, 1786), (32572, 1922), (38727, 1812), (43878, 1877),
  (47453, 1837), (57595, 1691), (72129, 1849), (72276, 1863), (73371, 1912),
  (78755, 1723), (82367, 1704), (87788, 1804), (88075, 1824), (89101, 1889),
  (89861, 1917), (96192, 1820), (104946, 1857), (106934, 1700), (111929, 1771),
  (121583, 1873)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y4_check. -/
theorem Z0Split62A0X0Y4_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk4
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y4_pairs. -/
theorem Z0Split62A0X0Y4_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S4096Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk4
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S4096Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S4096Chunk4
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S4096Chunk4_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S4096Chunk4_bound y hy)
  · exact Z0Split62A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y5Certs : List (Nat × Nat) := [
  (4357, 1978), (21040, 1992), (23427, 2074), (24929, 1980), (31787, 2083),
  (40872, 2176), (44488, 2145), (44591, 2154), (50175, 2014), (67613, 2043),
  (68262, 2063), (78481, 1997), (95165, 2012), (96564, 2053), (97501, 2113),
  (99104, 2008), (101038, 2064), (111341, 2005), (113889, 2114), (118565, 2168),
  (122773, 2174)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y5_check. -/
theorem Z0Split62A0X0Y5_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk5
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y5_pairs. -/
theorem Z0Split62A0X0Y5_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S4096Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk5
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S4096Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S4096Chunk5
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S4096Chunk5_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S4096Chunk5_bound y hy)
  · exact Z0Split62A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y6Certs : List (Nat × Nat) := [
  (2956, 2189), (2987, 2197), (3668, 2234), (5200, 2311), (13471, 2302),
  (18528, 2269), (30006, 2274), (30060, 2281), (33090, 2291), (37279, 2206),
  (37687, 2238), (38305, 2265), (43453, 2244), (47055, 2286), (49760, 2271),
  (66167, 2248), (67894, 2324), (78897, 2315)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y6_check. -/
theorem Z0Split62A0X0Y6_check : checkGrid m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk6
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y6_pairs. -/
theorem Z0Split62A0X0Y6_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S4096Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks1S256Chunk0 masks4S4096Chunk6
    (gridWords outerMasks1S256Chunk0 masks4S4096Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S4096Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S4096Chunk6
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S4096Chunk6_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks4S4096Chunk6_bound y hy)
  · exact Z0Split62A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0_pairs. -/
theorem Z0Split62A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split62A0X0Y0_pairs x hx y hy hw
  · exact Z0Split62A0X0Y1_pairs x hx y hy hw
  · exact Z0Split62A0X0Y2_pairs x hx y hy hw
  · exact Z0Split62A0X0Y3_pairs x hx y hy hw
  · exact Z0Split62A0X0Y4_pairs x hx y hy hw
  · exact Z0Split62A0X0Y5_pairs x hx y hy hw
  · exact Z0Split62A0X0Y6_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0_pairs. -/
theorem Z0Split62A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split62A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split62_check. -/
theorem Z0Split62_check : checkSplit m4TZ0 (1, 3, 4, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split62A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split63A0X0Y0Certs : List (Nat × Nat) := [
  (1964, 1256), (5984, 1228), (7155, 1828), (7240, 1881), (11352, 1904),
  (19166, 1742), (20147, 2241), (20251, 2299), (20967, 532), (21638, 923),
  (23599, 1952), (28405, 2316), (32739, 292), (34416, 1239), (34563, 1340),
  (39522, 1770), (40211, 2111), (40271, 2146), (40700, 187), (40920, 347),
  (42356, 1123), (45592, 696), (45903, 875), (47462, 1670), (47690, 1788),
  (48011, 1976), (49752, 782), (57559, 567), (57768, 690), (59918, 1817),
  (61181, 306), (61863, 714), (64696, 2172), (65485, 465), (66032, 793),
  (67627, 1604), (69949, 693), (70486, 988), (71478, 1507), (71528, 1520),
  (72886, 2208), (75254, 1385), (82608, 963), (83083, 1198), (84855, 2098),
  (86224, 717), (87108, 1182), (87167, 1217), (90150, 641), (90812, 999),
  (91552, 1410), (93561, 243), (94801, 972), (95153, 1147), (96701, 1962),
  (96956, 2051), (101682, 244), (102471, 742), (104648, 1860), (105716, 224),
  (106015, 428), (107863, 1456), (110210, 505), (110370, 584), (110762, 842),
  (112564, 1757), (112926, 1956), (114432, 585), (115723, 1312), (117506, 2195),
  (118138, 393), (119377, 1077), (119673, 1235), (120059, 1464), (121469, 2144)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0Y0_check. -/
theorem Z0Split63A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split63A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0Y0_pairs. -/
theorem Z0Split63A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split63A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks3S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact Z0Split63A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0_pairs. -/
theorem Z0Split63A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split63A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0_pairs. -/
theorem Z0Split63A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split63A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split63_check. -/
theorem Z0Split63_check : checkSplit m4TZ0 (1, 4, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split63A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split64A0X0Y0Certs : List (Nat × Nat) := [
  (88, 354), (376, 1901), (590, 633), (705, 1216), (786, 1737),
  (1057, 798), (1304, 2312), (1755, 97), (2114, 1880), (2148, 2097),
  (2398, 961), (2673, 250), (2908, 1422), (3650, 705), (3843, 1772),
  (3976, 239), (3983, 277), (4348, 2295), (4522, 738), (5120, 1594),
  (5370, 595), (5548, 1572), (6343, 1138), (6514, 2179), (6673, 579),
  (6684, 643), (6942, 2131), (7240, 1304), (7520, 494), (7856, 128),
  (8103, 1253), (8755, 232), (9053, 1741), (9201, 272), (9282, 573),
  (9406, 1227), (9609, 181), (10246, 1055), (11013, 546), (11287, 2107),
  (11422, 447), (12086, 1628), (12257, 298), (12439, 1152), (12851, 1035)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0X0Y0_check. -/
theorem Z0Split64A0X0Y0_check : checkGrid m4TZ0 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0X0Y0_pairs. -/
theorem Z0Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split64A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0X0_pairs. -/
theorem Z0Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0_pairs. -/
theorem Z0Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split64_check. -/
theorem Z0Split64_check : checkSplit m4TZ0 (1, 5, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split65A0X0Y0Certs : List (Nat × Nat) := [
  (19, 734), (84, 1291), (183, 49), (269, 2089), (367, 119),
  (431, 229), (553, 317), (617, 538), (773, 1135), (867, 1733)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0X0Y0_check. -/
theorem Z0Split65A0X0Y0_check : checkGrid m4TZ0 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0X0Y0_pairs. -/
theorem Z0Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split65A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0X0_pairs. -/
theorem Z0Split65A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0_pairs. -/
theorem Z0Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split65_check. -/
theorem Z0Split65_check : checkSplit m4TZ0 (1, 6, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0X0Y0_check. -/
theorem Z0Split66A0X0Y0_check : checkGrid m4TZ0 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0X0Y0_pairs. -/
theorem Z0Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split66A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0X0_pairs. -/
theorem Z0Split66A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0_pairs. -/
theorem Z0Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split66_check. -/
theorem Z0Split66_check : checkSplit m4TZ0 (1, 7, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A0X0Y0Certs : List (Nat × Nat) := [
  (71, 0), (118, 0), (326, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0X0Y0_check. -/
theorem Z0Split67A0X0Y0_check : checkGrid m4TZ0 3 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0X0Y0_pairs. -/
theorem Z0Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0X0_pairs. -/
theorem Z0Split67A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0_pairs. -/
theorem Z0Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1X0Y0_check. -/
theorem Z0Split67A1X0Y0_check : checkGrid m4TZ0 3 376821623 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1X0Y0_pairs. -/
theorem Z0Split67A1X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split67A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1X0_pairs. -/
theorem Z0Split67A1X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1_pairs. -/
theorem Z0Split67A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A2X0Y0Certs : List (Nat × Nat) := [
  (229, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2X0Y0_check. -/
theorem Z0Split67A2X0Y0_check : checkGrid m4TZ0 3 768556269 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2X0Y0_pairs. -/
theorem Z0Split67A2X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split67A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2X0_pairs. -/
theorem Z0Split67A2X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2_pairs. -/
theorem Z0Split67A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3X0Y0_check. -/
theorem Z0Split67A3X0Y0_check : checkGrid m4TZ0 3 1002105754 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3X0Y0_pairs. -/
theorem Z0Split67A3X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split67A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3X0_pairs. -/
theorem Z0Split67A3X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3_pairs. -/
theorem Z0Split67A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split67_check. -/
theorem Z0Split67_check : checkSplit m4TZ0 (2, 0, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split67A0_pairs x hx y hy hw
    · exact Z0Split67A1_pairs x hx y hy hw
    · exact Z0Split67A2_pairs x hx y hy hw
    · exact Z0Split67A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A0X0Y0Certs : List (Nat × Nat) := [
  (83, 0), (563, 677), (1107, 0), (1154, 0), (1241, 1329),
  (1468, 0), (1743, 1713), (2003, 0), (2217, 819), (3083, 0),
  (3467, 457), (3734, 1693), (4183, 1855), (4297, 1540), (4552, 0),
  (4739, 0), (4778, 0), (5009, 1348), (5141, 689), (5360, 0),
  (5537, 0), (5705, 0), (6270, 0), (6368, 0), (6478, 1497),
  (6803, 985), (6987, 1129), (7220, 1711), (7911, 0), (8357, 955),
  (8603, 0), (9899, 1652), (9923, 0), (10225, 858), (10868, 0),
  (10944, 899), (11004, 0), (11179, 0), (11538, 1541), (11649, 0),
  (11793, 0), (12066, 0), (12753, 1557), (12852, 0), (12924, 1109)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0X0Y0_check. -/
theorem Z0Split68A0X0Y0_check : checkGrid m4TZ0 3 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0X0Y0_pairs. -/
theorem Z0Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0X0_pairs. -/
theorem Z0Split68A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0_pairs. -/
theorem Z0Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A1X0Y0Certs : List (Nat × Nat) := [
  (809, 0), (1388, 2030), (1930, 0), (2220, 2084), (5706, 2076),
  (7993, 2086), (8617, 2067), (11806, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1X0Y0_check. -/
theorem Z0Split68A1X0Y0_check : checkGrid m4TZ0 3 376821623 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1X0Y0_pairs. -/
theorem Z0Split68A1X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split68A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1X0_pairs. -/
theorem Z0Split68A1X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1_pairs. -/
theorem Z0Split68A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A2X0Y0Certs : List (Nat × Nat) := [
  (2108, 0), (5012, 2276), (6092, 0), (6652, 0), (7097, 0),
  (7819, 2159), (8164, 0), (9072, 2205), (10622, 0), (10717, 0),
  (11119, 2169), (11634, 0), (11957, 0), (12617, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2X0Y0_check. -/
theorem Z0Split68A2X0Y0_check : checkGrid m4TZ0 3 768556269 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2X0Y0_pairs. -/
theorem Z0Split68A2X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split68A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2X0_pairs. -/
theorem Z0Split68A2X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2_pairs. -/
theorem Z0Split68A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3X0Y0_check. -/
theorem Z0Split68A3X0Y0_check : checkGrid m4TZ0 3 1002105754 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3X0Y0_pairs. -/
theorem Z0Split68A3X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split68A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3X0_pairs. -/
theorem Z0Split68A3X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3_pairs. -/
theorem Z0Split68A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split68_check. -/
theorem Z0Split68_check : checkSplit m4TZ0 (2, 1, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split68A0_pairs x hx y hy hw
    · exact Z0Split68A1_pairs x hx y hy hw
    · exact Z0Split68A2_pairs x hx y hy hw
    · exact Z0Split68A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A0X0Y0Certs : List (Nat × Nat) := [
  (110, 0), (1059, 0), (1301, 563), (4042, 0), (6519, 0),
  (6816, 0), (6928, 850), (7935, 0), (8019, 361), (8034, 0),
  (8061, 1872), (8654, 1188), (10448, 1518), (10799, 1910), (11087, 0),
  (11741, 1516), (12209, 0), (13363, 587), (14213, 716), (14500, 1417),
  (14983, 1722), (16855, 0), (17012, 1273), (19980, 0), (20695, 0),
  (22339, 0), (23538, 0), (24279, 679), (24347, 1785), (24759, 0),
  (25720, 0), (28423, 258), (28620, 0), (28662, 1655), (28914, 1106),
  (29966, 1476), (30306, 1411), (30935, 0), (32031, 811), (32769, 1841),
  (34697, 0), (37665, 953), (38846, 0), (39987, 1384), (41296, 991),
  (42592, 1243), (43642, 0), (43756, 1224), (44203, 666), (44475, 411),
  (44533, 0), (44559, 0), (45904, 0), (47586, 0), (47693, 0),
  (48296, 0), (48846, 1886), (49121, 0), (50010, 1281), (50142, 0),
  (50611, 0), (51820, 0), (53271, 0), (54097, 0), (54213, 0),
  (54382, 1612), (55740, 0), (55948, 453), (57044, 1596), (57288, 0),
  (57354, 1176), (58072, 0), (59917, 1407), (60443, 852), (60837, 1791),
  (62711, 0), (63131, 0), (65785, 0), (66233, 1372), (66391, 613),
  (67156, 0), (67745, 1681), (68777, 1887), (69813, 1521), (70354, 781),
  (72215, 1440), (72230, 942), (73826, 0), (74412, 1827), (74461, 588),
  (75337, 348), (75863, 0), (77150, 0), (78734, 0), (80157, 1044),
  (80283, 0), (80832, 672), (81489, 1053), (82842, 0), (83551, 1252),
  (85659, 0), (85752, 1171), (87663, 1238), (88154, 1839), (88361, 402),
  (89533, 1891), (89982, 646), (90257, 900), (90871, 1236), (93263, 0),
  (96341, 791), (96547, 0), (98076, 1924), (98886, 957), (99017, 1001),
  (103438, 1099), (104747, 0), (104875, 857), (104913, 0), (105461, 1597),
  (106667, 1073), (106947, 978), (107160, 0), (108025, 502), (108286, 1814),
  (110753, 718), (110865, 1218)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X0Y0_check. -/
theorem Z0Split69A0X0Y0_check : checkGrid m4TZ0 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X0Y0_pairs. -/
theorem Z0Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X0_pairs. -/
theorem Z0Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A0X1Y0Certs : List (Nat × Nat) := [
  (839, 1494), (1257, 1126), (1394, 1485), (1647, 1489), (4996, 358),
  (6087, 0), (8309, 570), (8489, 1060), (8616, 1284), (9739, 1245),
  (10005, 873), (10406, 1261), (10450, 1641), (11490, 794), (12549, 1625),
  (13545, 0), (13753, 1697), (15495, 0), (17193, 1614), (17282, 599),
  (17818, 755), (17903, 0), (18537, 1626), (19319, 1807), (20159, 885),
  (20418, 0), (20420, 0), (20609, 1347), (21374, 1004), (21624, 1420),
  (21848, 1900), (22566, 0), (22937, 868), (23110, 0), (23922, 0),
  (24937, 1806), (25650, 1043), (25807, 0), (26535, 1816), (27397, 0),
  (27545, 886), (29117, 349), (29161, 1558), (30023, 0), (30065, 0),
  (30450, 0), (30788, 0), (31691, 1013), (34576, 1104), (35245, 1706),
  (36819, 0), (37089, 1495), (37714, 533), (38351, 0), (38909, 1662),
  (39122, 979), (39931, 0), (40288, 1074), (41189, 0), (41879, 0),
  (41950, 0), (43432, 1231), (43474, 1882), (43642, 1859), (43872, 1664),
  (44165, 0), (44239, 0), (44847, 1896), (45788, 1663), (47039, 806),
  (48416, 0), (49561, 0), (50032, 808), (50046, 0), (50867, 0),
  (52754, 1211), (52826, 1636), (53043, 1923), (53127, 0), (55952, 1539),
  (56251, 688), (57565, 1327), (57813, 1474), (57924, 0), (57963, 0),
  (57969, 1724), (59561, 1509), (61530, 0), (61702, 0), (61744, 0),
  (61860, 0), (61971, 1613), (63772, 1542), (64439, 796), (67655, 1875),
  (67729, 1125), (68892, 161), (69586, 0), (69593, 1765), (70007, 1425),
  (71430, 0), (71876, 675), (71965, 0), (72434, 1426), (73379, 1388),
  (73441, 1439), (73660, 1432), (74440, 0), (75252, 0), (76165, 1434),
  (76451, 0), (77712, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X1Y0_check. -/
theorem Z0Split69A0X1Y0_check : checkGrid m4TZ0 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X1Y0_pairs. -/
theorem Z0Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X1_pairs. -/
theorem Z0Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0_pairs. -/
theorem Z0Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A0X0_pairs x hx y hy hw
  · exact Z0Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A1X0Y0Certs : List (Nat × Nat) := [
  (13851, 2087), (17759, 2009), (28535, 0), (32565, 2085), (33952, 1953),
  (37017, 2047), (37445, 0), (38669, 2048), (38773, 0), (45112, 2004),
  (52411, 0), (55898, 1994), (61296, 0), (62865, 2042), (66502, 2059),
  (69264, 1996), (72644, 0), (82712, 1982), (86489, 2011), (91721, 2065),
  (93928, 0), (94829, 0), (102885, 2025), (110632, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X0Y0_check. -/
theorem Z0Split69A1X0Y0_check : checkGrid m4TZ0 3 376821623 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X0Y0_pairs. -/
theorem Z0Split69A1X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X0_pairs. -/
theorem Z0Split69A1X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A1X1Y0Certs : List (Nat × Nat) := [
  (2418, 0), (18252, 0), (42147, 0), (45273, 2024), (46733, 2015),
  (46803, 2019), (53267, 2060), (53488, 0), (57572, 0), (64885, 2056)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X1Y0_check. -/
theorem Z0Split69A1X1Y0_check : checkGrid m4TZ0 3 376821623 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X1Y0_pairs. -/
theorem Z0Split69A1X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X1_pairs. -/
theorem Z0Split69A1X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1_pairs. -/
theorem Z0Split69A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A1X0_pairs x hx y hy hw
  · exact Z0Split69A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A2X0Y0Certs : List (Nat × Nat) := [
  (3446, 2268), (6854, 0), (11234, 0), (19701, 2309), (28576, 2293),
  (31991, 0), (32082, 2289), (43057, 2213), (50609, 2165), (50796, 2162),
  (53313, 2290), (57519, 0), (60272, 2204), (67061, 0), (69992, 0),
  (73054, 2264), (73347, 2275), (74826, 0), (75163, 2228), (79376, 0),
  (80241, 2288), (91181, 0), (92102, 2308), (97248, 2307), (98118, 0),
  (105620, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X0Y0_check. -/
theorem Z0Split69A2X0Y0_check : checkGrid m4TZ0 3 768556269 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X0Y0_pairs. -/
theorem Z0Split69A2X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X0_pairs. -/
theorem Z0Split69A2X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A2X1Y0Certs : List (Nat × Nat) := [
  (2147, 2218), (4314, 0), (9660, 2212), (24009, 0), (27064, 2273),
  (28694, 2300), (38446, 0), (40077, 2246), (44498, 0), (53687, 2147),
  (54230, 2237), (58493, 2153), (61600, 2236), (63083, 2250), (66217, 0),
  (67486, 2254), (69227, 2301), (69865, 2190), (71457, 2177), (71498, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X1Y0_check. -/
theorem Z0Split69A2X1Y0_check : checkGrid m4TZ0 3 768556269 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X1Y0_pairs. -/
theorem Z0Split69A2X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X1_pairs. -/
theorem Z0Split69A2X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2_pairs. -/
theorem Z0Split69A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A2X0_pairs x hx y hy hw
  · exact Z0Split69A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A3X0Y0Certs : List (Nat × Nat) := [
  (37395, 2323)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X0Y0_check. -/
theorem Z0Split69A3X0Y0_check : checkGrid m4TZ0 3 1002105754 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X0Y0_pairs. -/
theorem Z0Split69A3X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X0_pairs. -/
theorem Z0Split69A3X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A3X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X1Y0_check. -/
theorem Z0Split69A3X1Y0_check : checkGrid m4TZ0 3 1002105754 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X1Y0_pairs. -/
theorem Z0Split69A3X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X1_pairs. -/
theorem Z0Split69A3X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3_pairs. -/
theorem Z0Split69A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A3X0_pairs x hx y hy hw
  · exact Z0Split69A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split69_check. -/
theorem Z0Split69_check : checkSplit m4TZ0 (2, 2, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split69A0_pairs x hx y hy hw
    · exact Z0Split69A1_pairs x hx y hy hw
    · exact Z0Split69A2_pairs x hx y hy hw
    · exact Z0Split69A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y0Certs : List (Nat × Nat) := [
  (5505, 391), (9637, 400), (16564, 241), (32444, 248), (40563, 193),
  (48917, 302), (51881, 235), (52563, 357), (71200, 108), (110214, 215),
  (114963, 301)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y0_check. -/
theorem Z0Split70A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y0_pairs. -/
theorem Z0Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y1Certs : List (Nat × Nat) := [
  (23654, 514), (23753, 562), (28422, 596), (29280, 512), (35299, 760),
  (37421, 474), (49273, 520), (51436, 583), (57694, 655), (65619, 507),
  (72968, 597), (74009, 605), (77052, 593), (81325, 701), (89641, 473),
  (98234, 709), (102111, 575), (102334, 710), (105665, 559), (114230, 492),
  (126467, 462), (130272, 576)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y1_check. -/
theorem Z0Split70A0X0Y1_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y1_pairs. -/
theorem Z0Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y2Certs : List (Nat × Nat) := [
  (20345, 951), (24260, 871), (33860, 802), (37634, 882), (85439, 990),
  (104304, 943), (106063, 807), (108804, 884)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y2_check. -/
theorem Z0Split70A0X0Y2_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y2_pairs. -/
theorem Z0Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y3Certs : List (Nat × Nat) := [
  (15151, 1179), (23089, 1056), (39778, 1203), (63627, 1093), (63824, 1187),
  (71088, 1257), (72835, 1088), (84993, 1014), (87833, 1168), (88106, 1050),
  (101766, 1230), (102570, 1105), (103220, 1181), (105354, 1233), (121368, 1038),
  (123962, 1059), (125548, 1082)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y3_check. -/
theorem Z0Split70A0X0Y3_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y3_pairs. -/
theorem Z0Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y4Certs : List (Nat × Nat) := [
  (2442, 1502), (12709, 1510), (47771, 1397), (55720, 1512), (64941, 1513),
  (79574, 1427), (81472, 1355), (88058, 1533), (100422, 1358), (116734, 1535),
  (125557, 1378)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y4_check. -/
theorem Z0Split70A0X0Y4_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y4_pairs. -/
theorem Z0Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y5Certs : List (Nat × Nat) := [
  (7801, 1607), (8199, 1538), (29287, 1601), (33066, 1696), (37532, 1624),
  (59639, 1675), (62626, 1629), (65758, 1656), (77727, 1767), (84997, 1536),
  (94278, 1589), (123172, 1694)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y5_check. -/
theorem Z0Split70A0X0Y5_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y5_pairs. -/
theorem Z0Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y6Certs : List (Nat × Nat) := [
  (13269, 2036), (14724, 2016), (16010, 1895), (25688, 1871), (38365, 2038),
  (43955, 2026), (44102, 1854), (44558, 1823), (48196, 1852), (48652, 1821),
  (54066, 1981), (71361, 1920), (85665, 1905), (87123, 1865), (101732, 2007),
  (111588, 2041), (122939, 1838), (124908, 2044)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y6_check. -/
theorem Z0Split70A0X0Y6_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y6_pairs. -/
theorem Z0Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y7Certs : List (Nat × Nat) := [
  (8682, 2126), (8878, 2226), (13889, 2109), (14237, 2304), (16075, 2257),
  (33383, 2082), (45454, 2185), (46826, 2161), (54017, 2183), (55652, 2306),
  (62284, 2287), (68585, 2068), (77490, 2263), (81457, 2079), (88209, 2152),
  (88697, 2158), (90902, 2317), (93888, 2128), (94860, 2141), (102368, 2058),
  (108343, 2216), (120799, 2260), (120957, 2075)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y7_check. -/
theorem Z0Split70A0X0Y7_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y7_pairs. -/
theorem Z0Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0_pairs. -/
theorem Z0Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split70A0X0Y0_pairs x hx y hy hw
  · exact Z0Split70A0X0Y1_pairs x hx y hy hw
  · exact Z0Split70A0X0Y2_pairs x hx y hy hw
  · exact Z0Split70A0X0Y3_pairs x hx y hy hw
  · exact Z0Split70A0X0Y4_pairs x hx y hy hw
  · exact Z0Split70A0X0Y5_pairs x hx y hy hw
  · exact Z0Split70A0X0Y6_pairs x hx y hy hw
  · exact Z0Split70A0X0Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y0Certs : List (Nat × Nat) := [
  (2319, 297), (5701, 154), (20352, 389), (39562, 217), (55507, 257),
  (59296, 397)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y0_check. -/
theorem Z0Split70A0X1Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y0_pairs. -/
theorem Z0Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y1Certs : List (Nat × Nat) := [
  (26989, 663), (29291, 516), (30569, 662), (32503, 591), (44879, 649),
  (55732, 704), (69866, 581), (73399, 556), (80084, 568), (84154, 557),
  (85054, 495), (86820, 610)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y1_check. -/
theorem Z0Split70A0X1Y1_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y1_pairs. -/
theorem Z0Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y2Certs : List (Nat × Nat) := [
  (11968, 869), (15357, 1012), (20484, 780), (21165, 863), (23731, 864),
  (28812, 853), (47044, 995), (57372, 787), (89849, 879)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y2_check. -/
theorem Z0Split70A0X1Y2_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y2_pairs. -/
theorem Z0Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y3Certs : List (Nat × Nat) := [
  (1243, 1122), (5043, 1258), (6091, 1272), (9122, 1251), (16347, 1279),
  (24826, 1153), (30170, 1277), (30509, 1178), (30581, 1219), (34114, 1184),
  (38244, 1209), (45851, 1169), (49287, 1090), (51063, 1221), (66391, 1197),
  (72341, 1096), (74228, 1309), (75162, 1249), (81514, 1081), (85532, 1039),
  (86685, 1102)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y3_check. -/
theorem Z0Split70A0X1Y3_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y3_pairs. -/
theorem Z0Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y4Certs : List (Nat × Nat) := [
  (24185, 1380), (34531, 1433), (52769, 1339), (54371, 1370), (65938, 1503),
  (68598, 1530), (69949, 1482), (72017, 1486), (76826, 1333), (86055, 1341),
  (88733, 1398)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y4_check. -/
theorem Z0Split70A0X1Y4_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y4_pairs. -/
theorem Z0Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y5Certs : List (Nat × Nat) := [
  (4221, 1608), (4892, 1687), (11753, 1798), (12439, 1620), (14644, 1702),
  (15913, 1571), (25109, 1550), (25580, 1800), (30076, 1755), (30931, 1650),
  (33711, 1774), (41588, 1606), (43059, 1579), (44207, 1635), (45817, 1676),
  (53846, 1595), (58072, 1653), (67505, 1775), (76631, 1720), (79136, 1689)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y5_check. -/
theorem Z0Split70A0X1Y5_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y5_pairs. -/
theorem Z0Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y6Certs : List (Nat × Nat) := [
  (1702, 1906), (31251, 1825), (49927, 1969), (58025, 1907), (58924, 1836),
  (61587, 1898), (67836, 1964), (68364, 1971), (72896, 1918), (73224, 1818),
  (73328, 1883), (75815, 1832), (81126, 1954), (81523, 1885)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y6_check. -/
theorem Z0Split70A0X1Y6_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y6_pairs. -/
theorem Z0Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y7Certs : List (Nat × Nat) := [
  (2189, 2210), (8768, 2167), (10519, 2072), (10570, 2121), (25017, 2203),
  (40376, 2272), (47322, 2166), (51399, 2318), (58773, 2180), (63146, 2229),
  (67730, 2142), (69261, 2194), (71870, 2319), (83674, 2262), (84801, 2101)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y7_check. -/
theorem Z0Split70A0X1Y7_check : checkGrid m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y7_pairs. -/
theorem Z0Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1_pairs. -/
theorem Z0Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split70A0X1Y0_pairs x hx y hy hw
  · exact Z0Split70A0X1Y1_pairs x hx y hy hw
  · exact Z0Split70A0X1Y2_pairs x hx y hy hw
  · exact Z0Split70A0X1Y3_pairs x hx y hy hw
  · exact Z0Split70A0X1Y4_pairs x hx y hy hw
  · exact Z0Split70A0X1Y5_pairs x hx y hy hw
  · exact Z0Split70A0X1Y6_pairs x hx y hy hw
  · exact Z0Split70A0X1Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0_pairs. -/
theorem Z0Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split70A0X0_pairs x hx y hy hw
  · exact Z0Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split70_check. -/
theorem Z0Split70_check : checkSplit m4TZ0 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split71A0X0Y0Certs : List (Nat × Nat) := [
  (3462, 2133), (5809, 630), (6699, 744), (8250, 2156), (11738, 2224),
  (12584, 2055), (12972, 1754), (13032, 2132), (13997, 299), (14056, 542),
  (16448, 1740), (17547, 574), (20190, 764), (21904, 629), (22089, 1611),
  (22626, 64), (24969, 745), (27786, 1943), (27818, 2116), (28100, 1156),
  (28888, 756), (29863, 1316), (31956, 860), (33508, 81), (34582, 928),
  (36510, 2071), (38616, 1598), (40156, 544), (40488, 153), (41472, 572),
  (41743, 2140), (41829, 278), (43213, 580), (43670, 707), (43755, 1145),
  (46280, 706), (47265, 1322), (47827, 2106), (49172, 101), (49860, 1214),
  (50565, 424), (50611, 602), (54231, 1361), (54789, 2120), (54803, 2223),
  (55711, 151), (55789, 435), (56556, 65), (56745, 847), (57176, 838),
  (57893, 176), (60821, 1749), (61706, 1833), (62053, 1315), (62867, 987),
  (65285, 158), (65339, 359), (66049, 1779), (67714, 1350), (69246, 328),
  (72527, 1501), (74002, 218), (74786, 2034), (76204, 324), (78105, 1048),
  (79149, 2119), (81486, 552), (83250, 664), (84170, 925), (84645, 1143),
  (85361, 396), (86283, 627), (86729, 660), (86835, 1215), (87160, 645),
  (87578, 558), (87703, 1193), (89011, 1226), (89428, 1139), (89532, 1752),
  (92218, 2296), (93343, 1137), (93607, 331), (94503, 431), (94994, 661),
  (95342, 300), (97512, 284), (98249, 1878), (98957, 916), (99019, 1264),
  (101997, 881), (102923, 1166), (102983, 1532), (104613, 919), (104937, 398),
  (105171, 1599), (106673, 390), (106794, 933), (107483, 177), (107755, 1470),
  (108184, 1457), (108861, 439), (110188, 521), (110506, 99), (110842, 1738)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X0Y0_check. -/
theorem Z0Split71A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X0Y0_pairs. -/
theorem Z0Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X0_pairs. -/
theorem Z0Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split71A0X1Y0Certs : List (Nat × Nat) := [
  (2156, 2127), (2563, 1960), (3476, 2259), (3528, 209), (3563, 337),
  (3658, 757), (3827, 1684), (3996, 327), (5039, 1141), (7499, 405),
  (7583, 809), (8255, 2191), (9929, 1763), (12790, 748), (13833, 1695),
  (15130, 1618), (15762, 399), (18533, 1165), (21033, 626), (21529, 922),
  (21634, 1511), (22231, 205), (22692, 283), (23412, 1753), (24270, 1667),
  (24566, 878), (25231, 35), (25801, 543), (26039, 1879), (26178, 323),
  (26801, 1183), (26907, 1847), (28191, 1736), (28628, 1739), (28693, 2138),
  (31687, 1796), (32412, 946), (32429, 1041), (33383, 1531), (33777, 1310),
  (34732, 1797), (34770, 2070), (35067, 1186), (36562, 121), (37116, 553),
  (37182, 880), (38821, 426), (38918, 870), (39696, 440), (39979, 1989),
  (40407, 1958), (40677, 945), (42047, 1337), (42445, 1107), (43135, 280),
  (43475, 2102), (43613, 450), (44864, 236), (45235, 2252), (46240, 511),
  (46344, 1028), (46393, 1314), (46454, 1649), (47111, 515), (47543, 504),
  (48674, 1967), (48847, 499), (48901, 772), (49009, 1351), (49050, 1578),
  (49333, 758), (50380, 1747), (52409, 892), (52499, 1436), (53669, 659),
  (53917, 2108), (56611, 240), (56986, 36), (57457, 175), (57822, 2039),
  (57971, 458), (58849, 490), (59325, 665), (60013, 2139), (60770, 1459),
  (61222, 1528), (61787, 100), (62460, 1142), (62638, 2294), (62813, 741),
  (63445, 1829), (63482, 2095), (64353, 2096), (65539, 1352), (67129, 549),
  (68209, 1709), (69229, 251), (69327, 652), (69824, 970), (71398, 234),
  (71485, 566), (72726, 326), (72892, 1087), (72926, 1307), (72977, 1587),
  (73763, 1094), (74195, 1076), (74964, 560), (75305, 213), (75429, 743),
  (75499, 1067), (75547, 1369), (76540, 2122), (77754, 1544), (77784, 1744)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X1Y0_check. -/
theorem Z0Split71A0X1Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X1Y0_pairs. -/
theorem Z0Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X1_pairs. -/
theorem Z0Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0_pairs. -/
theorem Z0Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split71A0X0_pairs x hx y hy hw
  · exact Z0Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split71_check. -/
theorem Z0Split71_check : checkSplit m4TZ0 (2, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split72A0X0Y0Certs : List (Nat × Nat) := [
  (150, 4), (212, 34), (318, 621), (812, 33), (872, 29),
  (1206, 94), (1351, 18), (1410, 11), (2706, 87), (2778, 625),
  (2856, 93), (2972, 30), (3417, 1734), (3432, 262), (3664, 61),
  (3782, 32), (4761, 908), (5682, 266), (5741, 227), (5820, 7),
  (5982, 269), (6126, 91), (6330, 10), (6552, 270), (6749, 2093),
  (6768, 619), (7119, 170), (7296, 85), (7923, 46), (8298, 622),
  (9137, 539), (9272, 27), (9468, 624), (9612, 261), (10125, 416),
  (10302, 264), (10879, 733), (11047, 112), (11580, 9), (11633, 1136),
  (11796, 90), (11970, 5), (12108, 618), (12714, 1289), (12883, 316)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0X0Y0_check. -/
theorem Z0Split72A0X0Y0_check : checkGrid m4TZ0 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0X0Y0_pairs. -/
theorem Z0Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split72A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0X0_pairs. -/
theorem Z0Split72A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0_pairs. -/
theorem Z0Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split72_check. -/
theorem Z0Split72_check : checkSplit m4TZ0 (2, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0X0Y0_check. -/
theorem Z0Split73A0X0Y0_check : checkGrid m4TZ0 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0X0Y0_pairs. -/
theorem Z0Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split73A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0X0_pairs. -/
theorem Z0Split73A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0_pairs. -/
theorem Z0Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split73_check. -/
theorem Z0Split73_check : checkSplit m4TZ0 (2, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A0X0Y0Certs : List (Nat × Nat) := [
  (175, 1682), (388, 0), (413, 670), (435, 1009), (727, 1401),
  (1013, 600), (1026, 1728), (1269, 723), (1303, 1415), (1523, 1911),
  (1778, 0), (1840, 859), (1897, 1429), (2143, 1262), (2420, 334),
  (2546, 1267), (2634, 1364), (3085, 1498), (3168, 1633), (3509, 767),
  (3622, 1790), (3647, 0), (3951, 1874), (3997, 1085)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X0Y0_check. -/
theorem Z0Split74A0X0Y0_check : checkGrid m4TZ0 3 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X0Y0_pairs. -/
theorem Z0Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X0_pairs. -/
theorem Z0Split74A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0_pairs. -/
theorem Z0Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split74A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A1X0Y0Certs : List (Nat × Nat) := [
  (705, 2054), (1858, 2078), (2166, 2061), (3732, 2031)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X0Y0_check. -/
theorem Z0Split74A1X0Y0_check : checkGrid m4TZ0 3 376821623 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X0Y0_pairs. -/
theorem Z0Split74A1X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X0_pairs. -/
theorem Z0Split74A1X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1_pairs. -/
theorem Z0Split74A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split74A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A2X0Y0Certs : List (Nat × Nat) := [
  (67, 2217), (169, 2292), (3111, 2247), (3358, 2186), (3543, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X0Y0_check. -/
theorem Z0Split74A2X0Y0_check : checkGrid m4TZ0 3 768556269 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X0Y0_pairs. -/
theorem Z0Split74A2X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X0_pairs. -/
theorem Z0Split74A2X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2_pairs. -/
theorem Z0Split74A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split74A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A3X0Y0Certs : List (Nat × Nat) := [
  (2322, 2321), (3186, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X0Y0_check. -/
theorem Z0Split74A3X0Y0_check : checkGrid m4TZ0 3 1002105754 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X0Y0_pairs. -/
theorem Z0Split74A3X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X0_pairs. -/
theorem Z0Split74A3X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3_pairs. -/
theorem Z0Split74A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split74A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split74_check. -/
theorem Z0Split74_check : checkSplit m4TZ0 (3, 0, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split74A0_pairs x hx y hy hw
    · exact Z0Split74A1_pairs x hx y hy hw
    · exact Z0Split74A2_pairs x hx y hy hw
    · exact Z0Split74A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A0X0Y0Certs : List (Nat × Nat) := [
  (3445, 954), (3600, 1282), (3915, 0), (4320, 1477), (4425, 0),
  (4734, 0), (6443, 0), (6649, 974), (7053, 1514), (7460, 1657),
  (9548, 0), (14208, 1189), (15093, 1386), (15418, 0), (16588, 676),
  (17042, 1921), (17442, 0), (17932, 0), (18518, 0), (19089, 0),
  (19138, 0), (19224, 1677), (19568, 0), (20313, 0), (22237, 1205),
  (22980, 1813), (24525, 0), (24883, 1802), (24943, 695), (25014, 872),
  (25608, 0), (26563, 0), (27026, 0), (27269, 1330), (27295, 1381),
  (27463, 1349), (27751, 0), (30186, 1098), (31847, 0), (32434, 0),
  (34391, 472), (34678, 1200), (35239, 1359), (35597, 0), (36529, 1616),
  (36949, 699), (40243, 0), (40919, 0), (41088, 1858), (42090, 1842),
  (42362, 517), (43717, 105), (44658, 611), (45968, 803), (46539, 0),
  (46622, 0), (47820, 0), (48583, 294), (48809, 191), (49413, 0),
  (51513, 1554), (51726, 1124), (54777, 0), (54815, 722), (56681, 0),
  (57583, 1867), (59281, 0), (61128, 851), (61974, 1005), (62205, 0),
  (62914, 0), (64002, 1705), (66587, 1006), (66663, 0), (69368, 0),
  (70157, 1011), (70463, 1387), (70674, 1671), (70845, 0), (71048, 1862),
  (71235, 0), (71348, 0), (71910, 0), (72114, 889), (73248, 1815),
  (73634, 1428), (74124, 898), (74784, 1010), (74951, 412), (77354, 0),
  (79350, 0), (79464, 0), (79673, 0), (81522, 1602), (83269, 698),
  (83561, 469), (84042, 1177), (86862, 1647), (88058, 0), (90643, 0),
  (90853, 1632), (91592, 1793), (91960, 1265), (94538, 0), (94961, 0),
  (95794, 0), (96636, 1831), (97305, 0), (97868, 0), (98480, 1621),
  (98935, 0), (99041, 0), (100158, 1237), (100988, 0), (101083, 763),
  (101239, 0), (101633, 1488), (102117, 638), (102423, 1517), (104243, 1559),
  (104523, 1524), (105873, 1555), (107463, 1484), (107717, 901), (111333, 1639),
  (111821, 0), (112226, 0), (112543, 1046), (113102, 0), (114022, 0),
  (115879, 1078), (116456, 958), (117496, 1766)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X0Y0_check. -/
theorem Z0Split75A0X0Y0_check : checkGrid m4TZ0 3 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X0Y0_pairs. -/
theorem Z0Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 3 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X0_pairs. -/
theorem Z0Split75A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0_pairs. -/
theorem Z0Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split75A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A1X0Y0Certs : List (Nat × Nat) := [
  (19352, 1998), (20326, 0), (26527, 2045), (29256, 2080), (42147, 2018),
  (54157, 2049), (61422, 0), (62737, 0), (62951, 0), (69847, 1979),
  (71997, 2077), (86647, 2035), (88657, 2062), (100507, 2013), (120174, 2027)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X0Y0_check. -/
theorem Z0Split75A1X0Y0_check : checkGrid m4TZ0 3 376821623 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X0Y0_pairs. -/
theorem Z0Split75A1X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 3 376821623 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X0_pairs. -/
theorem Z0Split75A1X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1_pairs. -/
theorem Z0Split75A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split75A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A2X0Y0Certs : List (Nat × Nat) := [
  (1102, 0), (4249, 2232), (6358, 0), (14310, 2184), (24352, 0),
  (26852, 2277), (31532, 0), (39698, 0), (47466, 2225), (53411, 0),
  (55969, 0), (56058, 0), (58682, 2245), (58730, 0), (58954, 0),
  (61872, 2173), (91252, 2163), (94214, 0), (95827, 0), (95899, 2270),
  (99975, 0), (101040, 0), (102008, 0), (102536, 0), (103064, 2230),
  (103547, 0), (104429, 2214), (106170, 2249), (111107, 0), (111234, 0),
  (116837, 0), (116976, 2220), (118722, 2256)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X0Y0_check. -/
theorem Z0Split75A2X0Y0_check : checkGrid m4TZ0 3 768556269 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X0Y0_pairs. -/
theorem Z0Split75A2X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 3 768556269 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X0_pairs. -/
theorem Z0Split75A2X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2_pairs. -/
theorem Z0Split75A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split75A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A3X0Y0Certs : List (Nat × Nat) := [
  (6022, 0), (64552, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X0Y0_check. -/
theorem Z0Split75A3X0Y0_check : checkGrid m4TZ0 3 1002105754 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X0Y0_pairs. -/
theorem Z0Split75A3X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 3 1002105754 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X0_pairs. -/
theorem Z0Split75A3X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3_pairs. -/
theorem Z0Split75A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split75A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split75_check. -/
theorem Z0Split75_check : checkSplit m4TZ0 (3, 1, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split75A0_pairs x hx y hy hw
    · exact Z0Split75A1_pairs x hx y hy hw
    · exact Z0Split75A2_pairs x hx y hy hw
    · exact Z0Split75A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y0Certs : List (Nat × Nat) := [
  (296, 340), (17434, 104), (27928, 304), (29690, 456), (30502, 333),
  (30668, 432), (39169, 290), (45641, 155), (47423, 346), (52994, 291),
  (63614, 211), (72983, 303), (84329, 367), (85247, 287), (89945, 362),
  (93475, 330), (93565, 388), (93695, 460), (96692, 403), (98102, 344),
  (98272, 449), (98286, 452), (104261, 350), (107764, 285), (114776, 183),
  (114821, 214), (115051, 368)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y0_check. -/
theorem Z0Split76A0X0Y0_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y0_pairs. -/
theorem Z0Split76A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y1Certs : List (Nat × Nat) := [
  (1413, 674), (3723, 527), (4600, 774), (10349, 518), (12850, 489),
  (15863, 773), (16333, 747), (23867, 640), (58320, 750), (65672, 522),
  (69570, 712), (74739, 766), (86941, 684), (87960, 681), (93562, 667),
  (97892, 513), (106911, 686), (108389, 656), (117910, 529), (122966, 508)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y1_check. -/
theorem Z0Split76A0X0Y1_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y1_pairs. -/
theorem Z0Split76A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split76A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y2Certs : List (Nat × Nat) := [
  (2399, 940), (9751, 786), (10565, 927), (11382, 841), (22787, 883),
  (26033, 981), (31746, 779), (69745, 823), (73142, 984), (74573, 929),
  (97907, 824), (99374, 792), (109453, 971), (118614, 936)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y2_check. -/
theorem Z0Split76A0X0Y2_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y2_pairs. -/
theorem Z0Split76A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split76A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y3Certs : List (Nat × Nat) := [
  (2838, 1164), (16780, 1234), (20570, 1070), (20676, 1116), (24340, 1163),
  (39064, 1100), (42835, 1190), (44567, 1037), (59977, 1065), (66643, 1068),
  (85542, 1045), (86522, 1311), (89490, 1241), (103467, 1051), (125631, 1110),
  (129379, 1208)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y3_check. -/
theorem Z0Split76A0X0Y3_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y3_pairs. -/
theorem Z0Split76A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split76A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y4Certs : List (Nat × Nat) := [
  (21606, 1373), (38549, 1394), (42255, 1463), (49764, 1371), (50177, 1321),
  (55540, 1441), (58006, 1395), (58046, 1413), (76406, 1379), (96800, 1338),
  (108332, 1473), (114688, 1320), (114704, 1326), (115371, 1405), (130746, 1412)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y4_check. -/
theorem Z0Split76A0X0Y4_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y4_pairs. -/
theorem Z0Split76A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split76A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y5Certs : List (Nat × Nat) := [
  (5300, 1638), (9234, 1549), (14307, 1794), (45590, 1551), (51656, 1784),
  (58177, 1710), (58593, 1659), (58714, 1721), (60934, 1537), (64992, 1792),
  (86839, 1707), (95347, 1605), (97423, 1615), (103107, 1644), (110342, 1679),
  (116936, 1646), (118647, 1750), (126679, 1651)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y5_check. -/
theorem Z0Split76A0X0Y5_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y5_pairs. -/
theorem Z0Split76A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split76A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y6Certs : List (Nat × Nat) := [
  (3915, 1993), (37598, 1950), (38214, 1991), (91401, 1970), (92439, 1977),
  (92734, 1843), (96529, 1973), (111170, 1850), (115475, 1974), (120070, 1968)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y6_check. -/
theorem Z0Split76A0X0Y6_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y6_pairs. -/
theorem Z0Split76A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split76A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y7Certs : List (Nat × Nat) := [
  (7065, 2285), (20992, 2073), (27218, 2110), (37696, 2117), (38928, 2261),
  (43139, 2221), (53885, 2118), (56767, 2130), (86765, 2136), (97842, 2202),
  (103792, 2057), (109542, 2081), (115646, 2314), (115964, 2219)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y7_check. -/
theorem Z0Split76A0X0Y7_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y7_pairs. -/
theorem Z0Split76A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split76A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0_pairs. -/
theorem Z0Split76A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split76A0X0Y0_pairs x hx y hy hw
  · exact Z0Split76A0X0Y1_pairs x hx y hy hw
  · exact Z0Split76A0X0Y2_pairs x hx y hy hw
  · exact Z0Split76A0X0Y3_pairs x hx y hy hw
  · exact Z0Split76A0X0Y4_pairs x hx y hy hw
  · exact Z0Split76A0X0Y5_pairs x hx y hy hw
  · exact Z0Split76A0X0Y6_pairs x hx y hy hw
  · exact Z0Split76A0X0Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y0Certs : List (Nat × Nat) := [
  (6497, 365), (31262, 107), (36809, 430), (38391, 454), (44315, 309),
  (50618, 409), (51715, 52), (64934, 401), (67730, 219), (74507, 296),
  (76896, 185), (77347, 123), (82998, 133), (83513, 150)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y0_check. -/
theorem Z0Split76A0X1Y0_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y0_pairs. -/
theorem Z0Split76A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y1Certs : List (Nat × Nat) := [
  (1478, 721), (5057, 711), (10417, 551), (17138, 586), (18337, 694),
  (19214, 598), (19339, 678), (19428, 762), (21406, 685), (22355, 650),
  (39115, 564), (53166, 702), (63794, 634)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y1_check. -/
theorem Z0Split76A0X1Y1_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y1_pairs. -/
theorem Z0Split76A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split76A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y2Certs : List (Nat × Nat) := [
  (117, 840), (11551, 895), (14938, 812), (19132, 867), (19390, 989),
  (22297, 888), (22900, 947), (23826, 887), (24606, 788), (24969, 968),
  (24994, 976), (32313, 797), (52325, 817), (59494, 818), (59854, 998),
  (62853, 966), (67123, 795), (67457, 964), (80673, 896)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y2_check. -/
theorem Z0Split76A0X1Y2_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y2_pairs. -/
theorem Z0Split76A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split76A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y3Certs : List (Nat × Nat) := [
  (272, 1162), (442, 1259), (4766, 1103), (8496, 1180), (23251, 1118),
  (24713, 1092), (43123, 1083), (44604, 1061), (54185, 1255), (58196, 1194),
  (83965, 1318), (84038, 1064)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y3_check. -/
theorem Z0Split76A0X1Y3_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y3_pairs. -/
theorem Z0Split76A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split76A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y4Certs : List (Nat × Nat) := [
  (66, 1357), (417, 1508), (6237, 1363), (24805, 1438), (27318, 1408),
  (33593, 1481), (46609, 1328), (50581, 1505), (52493, 1462), (65833, 1472),
  (67232, 1400), (70630, 1529), (74951, 1418), (77324, 1323)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y4_check. -/
theorem Z0Split76A0X1Y4_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y4_pairs. -/
theorem Z0Split76A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split76A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y5Certs : List (Nat × Nat) := [
  (25141, 1580), (31896, 1622), (45906, 1714), (52698, 1789), (57902, 1576),
  (64875, 1726), (67362, 1692), (67442, 1745)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y5_check. -/
theorem Z0Split76A0X1Y5_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y5_pairs. -/
theorem Z0Split76A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split76A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y6Certs : List (Nat × Nat) := [
  (13867, 1835), (35926, 1870), (52400, 1908), (52581, 2010), (60941, 1822),
  (63328, 2003), (76865, 1848), (80589, 1939), (83732, 1975), (85147, 1903)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y6_check. -/
theorem Z0Split76A0X1Y6_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y6_pairs. -/
theorem Z0Split76A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split76A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y7Certs : List (Nat × Nat) := [
  (17530, 2278), (21774, 2255), (33913, 2129), (72976, 2151), (77877, 2215),
  (78063, 2320)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y7_check. -/
theorem Z0Split76A0X1Y7_check : checkGrid m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y7_pairs. -/
theorem Z0Split76A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
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
      exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split76A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1_pairs. -/
theorem Z0Split76A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split76A0X1Y0_pairs x hx y hy hw
  · exact Z0Split76A0X1Y1_pairs x hx y hy hw
  · exact Z0Split76A0X1Y2_pairs x hx y hy hw
  · exact Z0Split76A0X1Y3_pairs x hx y hy hw
  · exact Z0Split76A0X1Y4_pairs x hx y hy hw
  · exact Z0Split76A0X1Y5_pairs x hx y hy hw
  · exact Z0Split76A0X1Y6_pairs x hx y hy hw
  · exact Z0Split76A0X1Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0_pairs. -/
theorem Z0Split76A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split76A0X0_pairs x hx y hy hw
  · exact Z0Split76A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split76_check. -/
theorem Z0Split76_check : checkSplit m4TZ0 (3, 2, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X0Y0Certs : List (Nat × Nat) := [
  (9316, 771), (10680, 1049), (18178, 1642), (22067, 1500), (29359, 920),
  (44735, 1781), (49517, 1768), (76345, 939), (79196, 127), (81601, 1150),
  (85811, 459), (103387, 1365), (106915, 1619), (108261, 1940)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X0Y0_check. -/
theorem Z0Split77A0X0Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X0Y0_pairs. -/
theorem Z0Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X0_pairs. -/
theorem Z0Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X1Y0Certs : List (Nat × Nat) := [
  (2195, 106), (16158, 249), (17075, 437), (29289, 561), (29590, 78),
  (43031, 2032), (62005, 1031), (68332, 173), (84651, 1157), (88736, 2258),
  (90545, 255), (99930, 1493), (103676, 569)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X1Y0_check. -/
theorem Z0Split77A0X1Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X1Y0_pairs. -/
theorem Z0Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X1_pairs. -/
theorem Z0Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X2Y0Certs : List (Nat × Nat) := [
  (981, 441), (3390, 1666), (7386, 2199), (9845, 1276), (16953, 2170),
  (57097, 445), (73539, 125), (92255, 160), (93646, 487), (98207, 1584),
  (104488, 353), (106705, 510), (109108, 1760), (109337, 608), (110750, 1155)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X2Y0_check. -/
theorem Z0Split77A0X2Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X2Y0_pairs. -/
theorem Z0Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk2 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X2_pairs. -/
theorem Z0Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X3Y0Certs : List (Nat × Nat) := [
  (5447, 986), (9779, 894), (21398, 339), (22863, 1062), (23256, 861),
  (45084, 1301), (49922, 1586), (52434, 1027), (53455, 1951), (58940, 924),
  (60551, 345), (61370, 159), (70981, 295), (87830, 2002), (90912, 2283),
  (97965, 364), (102276, 216), (104985, 594), (106360, 938), (106666, 382)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X3Y0_check. -/
theorem Z0Split77A0X3Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X3Y0_pairs. -/
theorem Z0Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk3 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X3_pairs. -/
theorem Z0Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X4Y0Certs : List (Nat × Nat) := [
  (11586, 1297), (16432, 1603), (21796, 204), (23757, 1185), (24407, 207),
  (45599, 1761), (51080, 790), (57089, 407), (76491, 1787), (77754, 1547),
  (79634, 147), (81355, 79), (84089, 524), (94935, 423), (95599, 1590),
  (98445, 530), (106684, 434)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X4Y0_check. -/
theorem Z0Split77A0X4Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X4Y0_pairs. -/
theorem Z0Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk4 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X4_pairs. -/
theorem Z0Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X5Y0Certs : List (Nat × Nat) := [
  (7209, 1101), (17062, 387), (19940, 1782), (31754, 2313), (33014, 1966),
  (40607, 607), (56488, 1869), (59397, 1036), (64344, 2023), (69106, 1902),
  (70739, 1207), (74119, 700), (76423, 1423), (85047, 944), (87740, 1460),
  (94271, 1478), (97675, 1032), (98252, 1915), (106011, 1461), (108579, 1173)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X5Y0_check. -/
theorem Z0Split77A0X5Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X5Y0_pairs. -/
theorem Z0Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk5 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X5_pairs. -/
theorem Z0Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X6Y0Certs : List (Nat × Nat) := [
  (2841, 1024), (7675, 1305), (15033, 1063), (15674, 82), (19663, 351),
  (22078, 1575), (80698, 960), (109705, 343)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X6Y0_check. -/
theorem Z0Split77A0X6Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X6Y0_pairs. -/
theorem Z0Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk6 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X6_pairs. -/
theorem Z0Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X7Y0Certs : List (Nat × Nat) := [
  (3547, 274), (24695, 1593), (37129, 628), (41431, 427), (42734, 408),
  (45910, 1033), (52718, 338), (62827, 801), (65062, 1086), (69584, 2150),
  (69875, 1275), (71704, 1778), (80294, 1140), (83038, 1961), (86889, 1545),
  (104661, 1159), (110824, 1592)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X7Y0_check. -/
theorem Z0Split77A0X7Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X7Y0_pairs. -/
theorem Z0Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X7Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk7 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X7_pairs. -/
theorem Z0Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X8Y0Certs : List (Nat × Nat) := [
  (6066, 2105), (7020, 237), (18690, 2155), (24822, 132), (26724, 814),
  (34497, 519), (39423, 1254), (41011, 486), (41517, 839), (66995, 51),
  (74108, 639), (76022, 1585), (81904, 491), (85196, 1834), (86256, 497)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X8Y0_check. -/
theorem Z0Split77A0X8Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X8Y0_pairs. -/
theorem Z0Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X8Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk8 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X8_pairs. -/
theorem Z0Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X9Y0Certs : List (Nat × Nat) := [
  (5951, 1403), (7720, 1568), (8220, 1972), (13863, 1938), (15270, 203),
  (28049, 890), (35962, 1366), (39233, 335), (44738, 1809), (48827, 429),
  (61762, 2207), (63456, 1941), (66650, 386), (69212, 206), (72461, 1114),
  (88517, 917), (88850, 438), (94212, 1120), (105489, 935)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X9Y0_check. -/
theorem Z0Split77A0X9Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X9Y0_pairs. -/
theorem Z0Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X9Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk9 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X9_pairs. -/
theorem Z0Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X10Y0Certs : List (Nat × Nat) := [
  (13252, 865), (16086, 2200), (25992, 1570), (40059, 180), (44435, 253),
  (45344, 406), (59938, 1643), (60954, 223), (67612, 799), (71366, 129)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X10Y0_check. -/
theorem Z0Split77A0X10Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X10Y0_pairs. -/
theorem Z0Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X10Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk10 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X10_pairs. -/
theorem Z0Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X11Y0Certs : List (Nat × Nat) := [
  (33232, 740), (50588, 503), (60848, 1946), (72551, 1627), (73189, 433),
  (78919, 785), (88897, 636), (100431, 1944)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X11Y0_check. -/
theorem Z0Split77A0X11Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X11Y0_pairs. -/
theorem Z0Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X11Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk11 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X11_pairs. -/
theorem Z0Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X12Y0Certs : List (Nat × Nat) := [
  (2908, 1421), (10130, 493), (29151, 63), (31025, 550), (35014, 921),
  (36314, 893), (42094, 1591), (46457, 1683), (51511, 770), (59699, 404),
  (62822, 778), (63452, 1914), (65240, 2193), (76045, 1746), (101911, 485),
  (104360, 2001), (104599, 856)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X12Y0_check. -/
theorem Z0Split77A0X12Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X12Y0_pairs. -/
theorem Z0Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X12Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk12 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X12_pairs. -/
theorem Z0Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X13Y0Certs : List (Nat × Nat) := [
  (3426, 1942), (4489, 548), (9003, 1455), (12192, 80), (13211, 648),
  (22650, 149), (26222, 488), (29706, 496), (30341, 1569), (46869, 1546),
  (58089, 1029), (61653, 1504), (63256, 768), (70899, 2240), (76341, 926),
  (87785, 1719), (94016, 233), (95735, 156), (108100, 937), (109496, 1479)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X13Y0_check. -/
theorem Z0Split77A0X13Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X13Y0_pairs. -/
theorem Z0Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X13Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk13 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X13_pairs. -/
theorem Z0Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X14Y0Certs : List (Nat × Nat) := [
  (6541, 98), (16636, 425), (22255, 279), (31213, 1574), (46583, 178),
  (48095, 1075), (54609, 1026), (57035, 212), (70732, 1161), (71549, 891),
  (72698, 221), (73677, 651), (92456, 1034), (93744, 934), (102520, 1393)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X14Y0_check. -/
theorem Z0Split77A0X14Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X14Y0_pairs. -/
theorem Z0Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X14Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk14 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X14_pairs. -/
theorem Z0Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X15Y0Certs : List (Nat × Nat) := [
  (5691, 172), (12038, 1377), (21291, 2104), (21350, 157), (29386, 1054),
  (29617, 174), (50349, 1543), (51182, 1336), (68405, 436), (72975, 1577),
  (79897, 1368), (84370, 2123)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X15Y0_check. -/
theorem Z0Split77A0X15Y0_check : checkGrid m4TZ0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X15Y0_pairs. -/
theorem Z0Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X15Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk15 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X15_pairs. -/
theorem Z0Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0_pairs. -/
theorem Z0Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split77A0X0_pairs x hx y hy hw
  · exact Z0Split77A0X1_pairs x hx y hy hw
  · exact Z0Split77A0X2_pairs x hx y hy hw
  · exact Z0Split77A0X3_pairs x hx y hy hw
  · exact Z0Split77A0X4_pairs x hx y hy hw
  · exact Z0Split77A0X5_pairs x hx y hy hw
  · exact Z0Split77A0X6_pairs x hx y hy hw
  · exact Z0Split77A0X7_pairs x hx y hy hw
  · exact Z0Split77A0X8_pairs x hx y hy hw
  · exact Z0Split77A0X9_pairs x hx y hy hw
  · exact Z0Split77A0X10_pairs x hx y hy hw
  · exact Z0Split77A0X11_pairs x hx y hy hw
  · exact Z0Split77A0X12_pairs x hx y hy hw
  · exact Z0Split77A0X13_pairs x hx y hy hw
  · exact Z0Split77A0X14_pairs x hx y hy hw
  · exact Z0Split77A0X15_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split77_check. -/
theorem Z0Split77_check : checkSplit m4TZ0 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split78A0X0Y0Certs : List (Nat × Nat) := [
  (646, 483), (1837, 116), (4790, 836), (5424, 1293), (5486, 1562),
  (6430, 197), (6981, 904), (7132, 1018), (8881, 13), (9500, 833),
  (11608, 1925), (11743, 321), (14616, 92), (15585, 413), (17449, 736),
  (18784, 57), (20185, 1444), (20446, 480), (22057, 110), (22443, 47),
  (22565, 76), (22729, 727), (24286, 482), (24520, 198), (25933, 322),
  (26011, 17), (26140, 201), (26465, 72), (26666, 1563), (30484, 56),
  (32005, 1449), (36135, 419), (36668, 138), (36919, 735), (37398, 615),
  (40855, 1446), (42912, 265), (43666, 481), (44134, 60), (44451, 903),
  (47435, 75), (47602, 1022), (48285, 417), (48624, 1290), (50859, 168),
  (52918, 1930), (53662, 1021), (54519, 169), (57283, 315), (57907, 117),
  (58090, 200), (58254, 1288), (59461, 20), (60532, 1023), (61154, 380),
  (62857, 118), (64509, 163), (66808, 1936), (73551, 911), (73688, 144),
  (74414, 376), (74694, 1287), (75420, 2), (78465, 422), (81460, 196),
  (81481, 19), (81746, 1566), (82821, 909), (83168, 143), (83313, 48),
  (87964, 62), (88624, 59), (89743, 312), (89936, 1565), (91485, 414),
  (92356, 478), (95343, 45), (95539, 732), (98156, 1567), (98924, 377),
  (99392, 28), (106501, 15), (106563, 41), (107030, 832), (109672, 1020),
  (109955, 71), (110829, 171), (111463, 320), (112479, 165), (114289, 728),
  (114543, 44), (114575, 73), (116841, 905), (120217, 115), (120534, 1295)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X0Y0_check. -/
theorem Z0Split78A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X0Y0_pairs. -/
theorem Z0Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split78A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X0_pairs. -/
theorem Z0Split78A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0_pairs. -/
theorem Z0Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split78A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split78_check. -/
theorem Z0Split78_check : checkSplit m4TZ0 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X0Y0_check. -/
theorem Z0Split79A0X0Y0_check : checkGrid m4TZ0 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X0Y0_pairs. -/
theorem Z0Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split79A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X0_pairs. -/
theorem Z0Split79A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0_pairs. -/
theorem Z0Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split79A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split79_check. -/
theorem Z0Split79_check : checkSplit m4TZ0 (3, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split79A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split80A0X0Y0Certs : List (Nat × Nat) := [
  (152, 188), (170, 192), (1623, 466), (1694, 471), (2154, 523),
  (2237, 528), (3066, 637), (3795, 715), (6205, 948), (6604, 983),
  (6912, 1000), (7072, 1008), (8032, 1097), (8411, 1112), (8589, 1117),
  (8786, 1127), (9375, 1202), (9536, 1220), (10139, 1260), (10634, 1306),
  (10772, 1334), (12128, 1419), (15626, 1637), (15932, 1654), (16767, 1698),
  (16830, 1703), (17218, 1716), (17501, 1725), (18124, 1799), (18921, 1856),
  (19032, 1864), (19338, 1884), (20117, 1909), (20209, 1916), (20628, 1965),
  (21257, 2006), (23380, 2069), (24252, 2164), (24472, 2175), (24644, 2187),
  (25345, 2227), (25754, 2251), (26114, 2267), (26748, 2305), (27398, 2322)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y0_check. -/
theorem Z0Split80A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0Y0_pairs. -/
theorem Z0Split80A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split80A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks4S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks4S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S32768Chunk0_bound
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
      exact Z0M2Right_bound y (masks4S32768Chunk0_bound y hy)
  · exact Z0Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split80A0X0_pairs. -/
theorem Z0Split80A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split80A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split81A0X0Y0Certs : List (Nat × Nat) := [
  (45, 130), (870, 657), (6107, 1319), (6174, 1356), (7539, 2021),
  (8453, 355), (8785, 531), (13075, 671), (14489, 1458), (14709, 1526),
  (16544, 341), (17365, 816), (18719, 1515), (20486, 247), (25455, 804),
  (26112, 1121), (29395, 749), (31739, 1959), (31973, 2040), (33065, 501),
  (33079, 509), (37582, 783), (38585, 1317), (40106, 2046), (41360, 592),
  (47664, 1780), (48066, 1995), (50987, 1430), (51336, 1582), (52845, 152),
  (53321, 470), (54842, 1324), (58467, 1071), (58492, 1084), (61191, 329),
  (62071, 854), (63090, 1389), (66908, 1250), (70688, 1089), (72849, 2196),
  (73314, 282), (75836, 1645), (77547, 394), (77613, 442), (78655, 1007),
  (83986, 1660), (84023, 1680), (86232, 746), (86256, 761), (87658, 1491),
  (92533, 1897), (95468, 1342), (96225, 1688), (98698, 876), (98843, 952),
  (99655, 1404), (102480, 751), (103739, 1414), (109370, 2182), (110408, 603),
  (112415, 1668), (113804, 210), (115753, 1332), (119728, 1266), (120090, 1475)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0Y0_check. -/
theorem Z0Split81A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0Y0_pairs. -/
theorem Z0Split81A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split81A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S256Chunk0 masks3S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
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
      exact Z0M2Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact Z0Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split81A0X0_pairs. -/
theorem Z0Split81A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split81A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
  (106327, 800), (107403, 1983), (110580, 363), (110947, 122)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X0Y0_check. -/
theorem Z0Split82A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X0Y0_pairs. -/
theorem Z0Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X0Y0Certs
  · decide
  · decide
  · decide
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split82A0X1Y0Certs : List (Nat × Nat) := [
  (114, 451), (429, 2239), (771, 1600), (4078, 654), (5332, 444),
  (5927, 1247), (6491, 2033), (8981, 1308), (9528, 1984), (10325, 1519),
  (11203, 1573), (12844, 1003), (12892, 1299), (16135, 184), (16463, 1808),
  (17169, 874), (19885, 1469), (20001, 2201), (21029, 590), (21771, 120),
  (26885, 1718), (26918, 1947), (27328, 1759), (28443, 683), (31140, 1144),
  (32180, 2192), (37910, 254), (38066, 941), (38578, 1424), (39368, 931),
  (43254, 813), (44017, 332), (44595, 975), (44732, 1769), (44858, 220),
  (44939, 525), (45381, 554), (49275, 484), (50683, 959), (51270, 1894),
  (51689, 1762), (53489, 2149), (53715, 914), (55121, 1480), (55204, 1988),
  (57257, 1248), (58370, 325), (63128, 222), (63458, 1948), (65483, 1025),
  (65857, 739), (69441, 1296), (70236, 862), (70650, 765), (71116, 915),
  (71328, 2171), (71474, 526), (71591, 1115), (72038, 1167), (76969, 2100),
  (77415, 2157)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X1Y0_check. -/
theorem Z0Split82A0X1Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split82A0X1Y0_pairs. -/
theorem Z0Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split82A0X1Y0Certs
  · decide
  · decide
  · decide
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
  (58252, 1019), (58752, 263), (58829, 2090), (59570, 831), (60279, 166),
  (61377, 1732), (61738, 1933), (61915, 1450), (62671, 16), (63437, 537),
  (64481, 228), (65990, 834), (67705, 1452), (67789, 729), (70099, 730),
  (74748, 617), (75375, 418), (76340, 835), (78298, 1935), (79194, 1292),
  (79249, 731), (81833, 1134), (83459, 2091), (85063, 318), (88885, 1453),
  (93087, 1735), (93645, 420), (94808, 146), (95366, 1564), (95532, 268),
  (96041, 230), (96708, 620), (97905, 421), (98781, 907), (99602, 31),
  (101514, 1294), (103201, 21), (107400, 3), (108625, 1454), (109787, 540),
  (111460, 202), (112918, 1937), (114540, 6), (114921, 910), (118289, 2094),
  (119001, 912), (119460, 8), (119654, 381), (120215, 77), (120528, 623)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X0Y0_check. -/
theorem Z0Split83A0X0Y0_check : checkGrid m4TZ0 2 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X0Y0_pairs. -/
theorem Z0Split83A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split83A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks3S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0X0_pairs. -/
theorem Z0Split83A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split83A0_pairs. -/
theorem Z0Split83A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split83A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X0Y0_check. -/
theorem Z0Split84A0X0Y0_check : checkGrid m4TZ0 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X0Y0_pairs. -/
theorem Z0Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split84A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks4S32768Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks4S32768Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0X0_pairs. -/
theorem Z0Split84A0X0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split84A0_pairs. -/
theorem Z0Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split84A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split85A0X0Y0Certs : List (Nat × Nat) := [
  (179, 238), (211, 256), (691, 555), (734, 571), (804, 609),
  (1820, 1170), (1906, 1212), (2011, 1278), (2821, 1678), (3054, 1803),
  (3177, 1876), (3265, 1919), (3869, 2209), (3900, 2233), (3980, 2284)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0Y0_check. -/
theorem Z0Split85A0X0Y0_check : checkGrid m4TZ0 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0Y0_pairs. -/
theorem Z0Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split85A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
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
      exact Z0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact Z0Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split85A0X0_pairs. -/
theorem Z0Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split85A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split86A0X0Y0_check. -/
theorem Z0Split86A0X0Y0_check : checkGrid m4TZ0 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split86A0X0Y0_pairs. -/
theorem Z0Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split86A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
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
      exact Z0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact Z0Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split86A0X0_pairs. -/
theorem Z0Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split87A0X0Y0Certs : List (Nat × Nat) := [
  (470, 825), (1460, 827), (1988, 136), (2065, 1442), (3718, 1927),
  (3835, 1445), (4664, 372), (4798, 1928), (5300, 829), (5485, 1447),
  (7148, 141), (7348, 1931), (7688, 142), (8444, 375), (8605, 1451),
  (8818, 1934), (10154, 378), (10328, 145), (10754, 379), (12590, 837)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0X0Y0_check. -/
theorem Z0Split87A0X0Y0_check : checkGrid m4TZ0 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0X0Y0_pairs. -/
theorem Z0Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split87A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0X0_pairs. -/
theorem Z0Split87A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split87A0_pairs. -/
theorem Z0Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split88A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X0Y0_check. -/
theorem Z0Split88A0X0Y0_check : checkGrid m4TZ0 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X0Y0_pairs. -/
theorem Z0Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split88A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0X0_pairs. -/
theorem Z0Split88A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split88A0_pairs. -/
theorem Z0Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split88A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split89A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split89A0X0Y0_check. -/
theorem Z0Split89A0X0Y0_check : checkGrid m4TZ0 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split89A0X0Y0_pairs. -/
theorem Z0Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split89A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
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
      exact Z0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact Z0Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split89A0X0_pairs. -/
theorem Z0Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split90A0X0Y0Certs : List (Nat × Nat) := [
  (12, 259), (38, 134), (52, 1016), (78, 614), (134, 369),
  (146, 1560), (180, 0), (259, 726), (275, 70), (290, 826),
  (362, 24), (444, 1285), (460, 195), (475, 1443), (546, 86),
  (603, 40), (646, 479), (658, 1929), (757, 114), (853, 319)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0X0Y0_check. -/
theorem Z0Split90A0X0Y0_check : checkGrid m4TZ0 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0X0Y0_pairs. -/
theorem Z0Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split90A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact Z0Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0X0_pairs. -/
theorem Z0Split90A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split90A0_pairs. -/
theorem Z0Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0X0Y0_check. -/
theorem Z0Split91A0X0Y0_check : checkGrid m4TZ0 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0X0Y0_pairs. -/
theorem Z0Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split91A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0X0_pairs. -/
theorem Z0Split91A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split91A0_pairs. -/
theorem Z0Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0X0Y0_check. -/
theorem Z0Split92A0X0Y0_check : checkGrid m4TZ0 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0X0Y0_pairs. -/
theorem Z0Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split92A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact Z0Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0X0_pairs. -/
theorem Z0Split92A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split92A0_pairs. -/
theorem Z0Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0X0Y0_check. -/
theorem Z0Split93A0X0Y0_check : checkGrid m4TZ0 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0X0Y0_pairs. -/
theorem Z0Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split93A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact Z0Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0X0_pairs. -/
theorem Z0Split93A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split93A0_pairs. -/
theorem Z0Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 7 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0X0Y0_check. -/
theorem Z0Split94A0X0Y0_check : checkGrid m4TZ0 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0X0Y0_pairs. -/
theorem Z0Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 8 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split94A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact Z0Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0X0_pairs. -/
theorem Z0Split94A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 8 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for Z0Split94A0_pairs. -/
theorem Z0Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 8 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
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

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for checkAll_Z0. -/
theorem checkAll_Z0 : checkAll m4TZ0 splitsZ0 = true := by
  simp only [checkAll, splitsZ0, List.all_cons, List.all_nil,
    Z0Split0_check, Z0Split1_check, Z0Split2_check, Z0Split3_check,
    Z0Split4_check, Z0Split5_check, Z0Split6_check, Z0Split7_check,
    Z0Split8_check, Z0Split9_check, Z0Split10_check, Z0Split11_check,
    Z0Split12_check, Z0Split13_check, Z0Split14_check, Z0Split15_check,
    Z0Split16_check, Z0Split17_check, Z0Split18_check, Z0Split19_check,
    Z0Split20_check, Z0Split21_check, Z0Split22_check, Z0Split23_check,
    Z0Split24_check, Z0Split25_check, Z0Split26_check, Z0Split27_check,
    Z0Split28_check, Z0Split29_check, Z0Split30_check, Z0Split31_check,
    Z0Split32_check, Z0Split33_check, Z0Split34_check, Z0Split35_check,
    Z0Split36_check, Z0Split37_check, Z0Split38_check, Z0Split39_check,
    Z0Split40_check, Z0Split41_check, Z0Split42_check, Z0Split43_check,
    Z0Split44_check, Z0Split45_check, Z0Split46_check, Z0Split47_check,
    Z0Split48_check, Z0Split49_check, Z0Split50_check, Z0Split51_check,
    Z0Split52_check, Z0Split53_check, Z0Split54_check, Z0Split55_check,
    Z0Split56_check, Z0Split57_check, Z0Split58_check, Z0Split59_check,
    Z0Split60_check, Z0Split61_check, Z0Split62_check, Z0Split63_check,
    Z0Split64_check, Z0Split65_check, Z0Split66_check, Z0Split67_check,
    Z0Split68_check, Z0Split69_check, Z0Split70_check, Z0Split71_check,
    Z0Split72_check, Z0Split73_check, Z0Split74_check, Z0Split75_check,
    Z0Split76_check, Z0Split77_check, Z0Split78_check, Z0Split79_check,
    Z0Split80_check, Z0Split81_check, Z0Split82_check, Z0Split83_check,
    Z0Split84_check, Z0Split85_check, Z0Split86_check, Z0Split87_check,
    Z0Split88_check, Z0Split89_check, Z0Split90_check, Z0Split91_check,
    Z0Split92_check, Z0Split93_check, Z0Split94_check, Bool.and_true]

#print axioms checkAll_Z0

end Quantum.Stabilizer.Homological.LP.M150

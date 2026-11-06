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
def X0Split0A0X0Y0Certs : List (Nat × Nat) := [
  (0, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split0A0X0Y0_check. -/
theorem X0Split0A0X0Y0_check : checkGrid m4TX0 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split0A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split0A0X0Y0_pairs. -/
theorem X0Split0A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 0 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split0A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split0A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split0A0X0_pairs. -/
theorem X0Split0A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 0 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split0A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split0A0_pairs. -/
theorem X0Split0A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 0 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split0A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split0_check. -/
theorem X0Split0_check : checkSplit m4TX0 (0, 0, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split0A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split1A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split1A0X0Y0_check. -/
theorem X0Split1A0X0Y0_check : checkGrid m4TX0 1 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split1A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split1A0X0Y0_pairs. -/
theorem X0Split1A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split1A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split1A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split1A0X0_pairs. -/
theorem X0Split1A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split1A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split1A0_pairs. -/
theorem X0Split1A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split1A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split1_check. -/
theorem X0Split1_check : checkSplit m4TX0 (0, 0, 2, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split1A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split2A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split2A0X0Y0_check. -/
theorem X0Split2A0X0Y0_check : checkGrid m4TX0 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split2A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split2A0X0Y0_pairs. -/
theorem X0Split2A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 1 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split2A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split2A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split2A0X0_pairs. -/
theorem X0Split2A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 1 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split2A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split2A0_pairs. -/
theorem X0Split2A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 1 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split2A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split2_check. -/
theorem X0Split2_check : checkSplit m4TX0 (0, 1, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split2A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split3A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split3A0X0Y0_check. -/
theorem X0Split3A0X0Y0_check : checkGrid m4TX0 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split3A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split3A0X0Y0_pairs. -/
theorem X0Split3A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split3A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split3A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split3A0X0_pairs. -/
theorem X0Split3A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split3A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split3A0_pairs. -/
theorem X0Split3A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split3A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split3_check. -/
theorem X0Split3_check : checkSplit m4TX0 (0, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split3A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split4A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split4A0X0Y0_check. -/
theorem X0Split4A0X0Y0_check : checkGrid m4TX0 1 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split4A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split4A0X0Y0_pairs. -/
theorem X0Split4A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 1 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split4A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split4A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split4A0X0_pairs. -/
theorem X0Split4A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 1 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split4A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split4A0_pairs. -/
theorem X0Split4A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 1 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split4A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split4_check. -/
theorem X0Split4_check : checkSplit m4TX0 (1, 0, 1, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split4A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split5A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split5A0X0Y0_check. -/
theorem X0Split5A0X0Y0_check : checkGrid m4TX0 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split5A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split5A0X0Y0_pairs. -/
theorem X0Split5A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 1 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split5A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split5A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split5A0X0_pairs. -/
theorem X0Split5A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 1 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split5A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split5A0_pairs. -/
theorem X0Split5A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 1 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split5A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split5_check. -/
theorem X0Split5_check : checkSplit m4TX0 (1, 1, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split5A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split6A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A0X0Y0_check. -/
theorem X0Split6A0X0Y0_check : checkGrid m4TX0 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A0X0Y0_pairs. -/
theorem X0Split6A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 2 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split6A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A0X0_pairs. -/
theorem X0Split6A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 2 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split6A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A0_pairs. -/
theorem X0Split6A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 2 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split6A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split6A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A1X0Y0_check. -/
theorem X0Split6A1X0Y0_check : checkGrid m4TX0 2 91076351 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A1X0Y0_pairs. -/
theorem X0Split6A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 2 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split6A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A1X0_pairs. -/
theorem X0Split6A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 2 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split6A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A1_pairs. -/
theorem X0Split6A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 2 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split6A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split6A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A2X0Y0_check. -/
theorem X0Split6A2X0Y0_check : checkGrid m4TX0 2 985062231 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A2X0Y0_pairs. -/
theorem X0Split6A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 2 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split6A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A2X0_pairs. -/
theorem X0Split6A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 2 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split6A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A2_pairs. -/
theorem X0Split6A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 2 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split6A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split6A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A3X0Y0_check. -/
theorem X0Split6A3X0Y0_check : checkGrid m4TX0 2 1071345064 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A3X0Y0_pairs. -/
theorem X0Split6A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 2 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split6A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split6A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A3X0_pairs. -/
theorem X0Split6A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 2 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split6A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6A3_pairs. -/
theorem X0Split6A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 2 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split6A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split6_check. -/
theorem X0Split6_check : checkSplit m4TX0 (2, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split6A0_pairs x hx y hy hw
    · exact X0Split6A1_pairs x hx y hy hw
    · exact X0Split6A2_pairs x hx y hy hw
    · exact X0Split6A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split7A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split7A0X0Y0_check. -/
theorem X0Split7A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split7A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split7A0X0Y0_pairs. -/
theorem X0Split7A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split7A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split7A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split7A0X0_pairs. -/
theorem X0Split7A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split7A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split7A0_pairs. -/
theorem X0Split7A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split7A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split7_check. -/
theorem X0Split7_check : checkSplit m4TX0 (0, 0, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split7A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split8A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split8A0X0Y0_check. -/
theorem X0Split8A0X0Y0_check : checkGrid m4TX0 1 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split8A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split8A0X0Y0_pairs. -/
theorem X0Split8A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split8A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split8A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split8A0X0_pairs. -/
theorem X0Split8A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split8A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split8A0_pairs. -/
theorem X0Split8A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split8A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split8_check. -/
theorem X0Split8_check : checkSplit m4TX0 (0, 1, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split8A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split9A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split9A0X0Y0_check. -/
theorem X0Split9A0X0Y0_check : checkGrid m4TX0 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split9A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split9A0X0Y0_pairs. -/
theorem X0Split9A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split9A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split9A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split9A0X0_pairs. -/
theorem X0Split9A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split9A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split9A0_pairs. -/
theorem X0Split9A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split9A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split9_check. -/
theorem X0Split9_check : checkSplit m4TX0 (0, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split9A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split10A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split10A0X0Y0_check. -/
theorem X0Split10A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split10A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split10A0X0Y0_pairs. -/
theorem X0Split10A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split10A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split10A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split10A0X0_pairs. -/
theorem X0Split10A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split10A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split10A0_pairs. -/
theorem X0Split10A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split10A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split10_check. -/
theorem X0Split10_check : checkSplit m4TX0 (0, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split10A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split11A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split11A0X0Y0_check. -/
theorem X0Split11A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split11A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split11A0X0Y0_pairs. -/
theorem X0Split11A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split11A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split11A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split11A0X0_pairs. -/
theorem X0Split11A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split11A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split11A0_pairs. -/
theorem X0Split11A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split11A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split11_check. -/
theorem X0Split11_check : checkSplit m4TX0 (0, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split11A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split12A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split12A0X0Y0_check. -/
theorem X0Split12A0X0Y0_check : checkGrid m4TX0 1 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split12A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split12A0X0Y0_pairs. -/
theorem X0Split12A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split12A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split12A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split12A0X0_pairs. -/
theorem X0Split12A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split12A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split12A0_pairs. -/
theorem X0Split12A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split12A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split12_check. -/
theorem X0Split12_check : checkSplit m4TX0 (1, 0, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split12A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split13A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split13A0X0Y0_check. -/
theorem X0Split13A0X0Y0_check : checkGrid m4TX0 1 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split13A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split13A0X0Y0_pairs. -/
theorem X0Split13A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split13A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split13A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split13A0X0_pairs. -/
theorem X0Split13A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split13A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split13A0_pairs. -/
theorem X0Split13A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split13A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split13_check. -/
theorem X0Split13_check : checkSplit m4TX0 (1, 1, 2, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split13A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split14A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split14A0X0Y0_check. -/
theorem X0Split14A0X0Y0_check : checkGrid m4TX0 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split14A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split14A0X0Y0_pairs. -/
theorem X0Split14A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split14A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split14A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split14A0X0_pairs. -/
theorem X0Split14A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split14A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split14A0_pairs. -/
theorem X0Split14A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split14A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split14_check. -/
theorem X0Split14_check : checkSplit m4TX0 (1, 2, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split14A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split15A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split15A0X0Y0_check. -/
theorem X0Split15A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split15A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split15A0X0Y0_pairs. -/
theorem X0Split15A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split15A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split15A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split15A0X0_pairs. -/
theorem X0Split15A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split15A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split15A0_pairs. -/
theorem X0Split15A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split15A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split15_check. -/
theorem X0Split15_check : checkSplit m4TX0 (1, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split15A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split16A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split16A0X0Y0_check. -/
theorem X0Split16A0X0Y0_check : checkGrid m4TX0 1 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split16A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split16A0X0Y0_pairs. -/
theorem X0Split16A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split16A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split16A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split16A0X0_pairs. -/
theorem X0Split16A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split16A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split16A0_pairs. -/
theorem X0Split16A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 2 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split16A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split16_check. -/
theorem X0Split16_check : checkSplit m4TX0 (2, 0, 2, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split16A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split17A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A0X0Y0_check. -/
theorem X0Split17A0X0Y0_check : checkGrid m4TX0 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A0X0Y0_pairs. -/
theorem X0Split17A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 2 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split17A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A0X0_pairs. -/
theorem X0Split17A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 2 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split17A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A0_pairs. -/
theorem X0Split17A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 2 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split17A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split17A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A1X0Y0_check. -/
theorem X0Split17A1X0Y0_check : checkGrid m4TX0 2 91076351 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A1X0Y0_pairs. -/
theorem X0Split17A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 2 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split17A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A1X0_pairs. -/
theorem X0Split17A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 2 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split17A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A1_pairs. -/
theorem X0Split17A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 2 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split17A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split17A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A2X0Y0_check. -/
theorem X0Split17A2X0Y0_check : checkGrid m4TX0 2 985062231 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A2X0Y0_pairs. -/
theorem X0Split17A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 2 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split17A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A2X0_pairs. -/
theorem X0Split17A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 2 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split17A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A2_pairs. -/
theorem X0Split17A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 2 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split17A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split17A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A3X0Y0_check. -/
theorem X0Split17A3X0Y0_check : checkGrid m4TX0 2 1071345064 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A3X0Y0_pairs. -/
theorem X0Split17A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 2 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split17A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split17A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A3X0_pairs. -/
theorem X0Split17A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 2 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split17A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17A3_pairs. -/
theorem X0Split17A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 2 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split17A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split17_check. -/
theorem X0Split17_check : checkSplit m4TX0 (2, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split17A0_pairs x hx y hy hw
    · exact X0Split17A1_pairs x hx y hy hw
    · exact X0Split17A2_pairs x hx y hy hw
    · exact X0Split17A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split18A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split18A0X0Y0_check. -/
theorem X0Split18A0X0Y0_check : checkGrid m4TX0 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split18A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split18A0X0Y0_pairs. -/
theorem X0Split18A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split18A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split18A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split18A0X0_pairs. -/
theorem X0Split18A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split18A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split18A0_pairs. -/
theorem X0Split18A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split18A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split18_check. -/
theorem X0Split18_check : checkSplit m4TX0 (2, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split18A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split19A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A0X0Y0_check. -/
theorem X0Split19A0X0Y0_check : checkGrid m4TX0 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A0X0Y0_pairs. -/
theorem X0Split19A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split19A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A0X0_pairs. -/
theorem X0Split19A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split19A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A0_pairs. -/
theorem X0Split19A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split19A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split19A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A1X0Y0_check. -/
theorem X0Split19A1X0Y0_check : checkGrid m4TX0 2 91076351 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A1X0Y0_pairs. -/
theorem X0Split19A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split19A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A1X0_pairs. -/
theorem X0Split19A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split19A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A1_pairs. -/
theorem X0Split19A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split19A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split19A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A2X0Y0_check. -/
theorem X0Split19A2X0Y0_check : checkGrid m4TX0 2 985062231 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A2X0Y0_pairs. -/
theorem X0Split19A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split19A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A2X0_pairs. -/
theorem X0Split19A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split19A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A2_pairs. -/
theorem X0Split19A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split19A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split19A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A3X0Y0_check. -/
theorem X0Split19A3X0Y0_check : checkGrid m4TX0 2 1071345064 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A3X0Y0_pairs. -/
theorem X0Split19A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split19A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split19A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A3X0_pairs. -/
theorem X0Split19A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split19A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19A3_pairs. -/
theorem X0Split19A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split19A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split19_check. -/
theorem X0Split19_check : checkSplit m4TX0 (3, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split19A0_pairs x hx y hy hw
    · exact X0Split19A1_pairs x hx y hy hw
    · exact X0Split19A2_pairs x hx y hy hw
    · exact X0Split19A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split20A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A0X0Y0_check. -/
theorem X0Split20A0X0Y0_check : checkGrid m4TX0 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A0X0Y0_pairs. -/
theorem X0Split20A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split20A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A0X0_pairs. -/
theorem X0Split20A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split20A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A0_pairs. -/
theorem X0Split20A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split20A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split20A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A1X0Y0_check. -/
theorem X0Split20A1X0Y0_check : checkGrid m4TX0 2 91076351 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A1X0Y0_pairs. -/
theorem X0Split20A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split20A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A1X0_pairs. -/
theorem X0Split20A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split20A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A1_pairs. -/
theorem X0Split20A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split20A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split20A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A2X0Y0_check. -/
theorem X0Split20A2X0Y0_check : checkGrid m4TX0 2 985062231 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A2X0Y0_pairs. -/
theorem X0Split20A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split20A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A2X0_pairs. -/
theorem X0Split20A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split20A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A2_pairs. -/
theorem X0Split20A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split20A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split20A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A3X0Y0_check. -/
theorem X0Split20A3X0Y0_check : checkGrid m4TX0 2 1071345064 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A3X0Y0_pairs. -/
theorem X0Split20A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split20A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split20A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A3X0_pairs. -/
theorem X0Split20A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split20A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20A3_pairs. -/
theorem X0Split20A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split20A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split20_check. -/
theorem X0Split20_check : checkSplit m4TX0 (3, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split20A0_pairs x hx y hy hw
    · exact X0Split20A1_pairs x hx y hy hw
    · exact X0Split20A2_pairs x hx y hy hw
    · exact X0Split20A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split21A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A0X0Y0_check. -/
theorem X0Split21A0X0Y0_check : checkGrid m4TX0 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A0X0Y0_pairs. -/
theorem X0Split21A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split21A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A0X0_pairs. -/
theorem X0Split21A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split21A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A0_pairs. -/
theorem X0Split21A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split21A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split21A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A1X0Y0_check. -/
theorem X0Split21A1X0Y0_check : checkGrid m4TX0 2 91076351 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A1X0Y0_pairs. -/
theorem X0Split21A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split21A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A1X0_pairs. -/
theorem X0Split21A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split21A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A1_pairs. -/
theorem X0Split21A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split21A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split21A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A2X0Y0_check. -/
theorem X0Split21A2X0Y0_check : checkGrid m4TX0 2 985062231 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A2X0Y0_pairs. -/
theorem X0Split21A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split21A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A2X0_pairs. -/
theorem X0Split21A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split21A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A2_pairs. -/
theorem X0Split21A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split21A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split21A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A3X0Y0_check. -/
theorem X0Split21A3X0Y0_check : checkGrid m4TX0 2 1071345064 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A3X0Y0_pairs. -/
theorem X0Split21A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split21A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split21A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A3X0_pairs. -/
theorem X0Split21A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split21A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21A3_pairs. -/
theorem X0Split21A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split21A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split21_check. -/
theorem X0Split21_check : checkSplit m4TX0 (4, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split21A0_pairs x hx y hy hw
    · exact X0Split21A1_pairs x hx y hy hw
    · exact X0Split21A2_pairs x hx y hy hw
    · exact X0Split21A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split22A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split22A0X0Y0_check. -/
theorem X0Split22A0X0Y0_check : checkGrid m4TX0 1 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split22A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split22A0X0Y0_pairs. -/
theorem X0Split22A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split22A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split22A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split22A0X0_pairs. -/
theorem X0Split22A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split22A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split22A0_pairs. -/
theorem X0Split22A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split22A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split22_check. -/
theorem X0Split22_check : checkSplit m4TX0 (0, 0, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split22A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split23A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split23A0X0Y0_check. -/
theorem X0Split23A0X0Y0_check : checkGrid m4TX0 1 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split23A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split23A0X0Y0_pairs. -/
theorem X0Split23A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split23A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split23A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split23A0X0_pairs. -/
theorem X0Split23A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split23A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split23A0_pairs. -/
theorem X0Split23A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split23A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split23_check. -/
theorem X0Split23_check : checkSplit m4TX0 (0, 1, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split23A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split24A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split24A0X0Y0_check. -/
theorem X0Split24A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split24A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split24A0X0Y0_pairs. -/
theorem X0Split24A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split24A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split24A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split24A0X0_pairs. -/
theorem X0Split24A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split24A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split24A0_pairs. -/
theorem X0Split24A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split24A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split24_check. -/
theorem X0Split24_check : checkSplit m4TX0 (0, 2, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split24A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split25A0X0Y0Certs : List (Nat × Nat) := [
  (8, 65), (39, 120), (109, 177), (153, 211), (166, 234),
  (311, 318), (397, 363), (542, 433), (661, 488), (697, 521),
  (735, 536), (1056, 675), (1241, 758), (1516, 873), (1746, 981),
  (1843, 1037), (1909, 1066), (2210, 1174), (2235, 1194), (2237, 1195),
  (2506, 1309), (2922, 1489), (3090, 1580), (3184, 1628), (3598, 1784),
  (3606, 1792), (3609, 1793), (3807, 1894), (3818, 1900), (4017, 1985)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split25A0X0Y0_check. -/
theorem X0Split25A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split25A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split25A0X0Y0_pairs. -/
theorem X0Split25A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split25A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X0Split25A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split25A0X0_pairs. -/
theorem X0Split25A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split25A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split25A0_pairs. -/
theorem X0Split25A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split25A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split25_check. -/
theorem X0Split25_check : checkSplit m4TX0 (0, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split25A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split26A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split26A0X0Y0_check. -/
theorem X0Split26A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split26A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split26A0X0Y0_pairs. -/
theorem X0Split26A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split26A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split26A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split26A0X0_pairs. -/
theorem X0Split26A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split26A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split26A0_pairs. -/
theorem X0Split26A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split26A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split26_check. -/
theorem X0Split26_check : checkSplit m4TX0 (0, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split26A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split27A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split27A0X0Y0_check. -/
theorem X0Split27A0X0Y0_check : checkGrid m4TX0 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split27A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split27A0X0Y0_pairs. -/
theorem X0Split27A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split27A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split27A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split27A0X0_pairs. -/
theorem X0Split27A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split27A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split27A0_pairs. -/
theorem X0Split27A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split27A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split27_check. -/
theorem X0Split27_check : checkSplit m4TX0 (0, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split27A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split28A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split28A0X0Y0_check. -/
theorem X0Split28A0X0Y0_check : checkGrid m4TX0 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split28A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split28A0X0Y0_pairs. -/
theorem X0Split28A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split28A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split28A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split28A0X0_pairs. -/
theorem X0Split28A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split28A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split28A0_pairs. -/
theorem X0Split28A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split28A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split28_check. -/
theorem X0Split28_check : checkSplit m4TX0 (0, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split28A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split29A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split29A0X0Y0_check. -/
theorem X0Split29A0X0Y0_check : checkGrid m4TX0 1 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split29A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split29A0X0Y0_pairs. -/
theorem X0Split29A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split29A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split29A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split29A0X0_pairs. -/
theorem X0Split29A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split29A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split29A0_pairs. -/
theorem X0Split29A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split29A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split29_check. -/
theorem X0Split29_check : checkSplit m4TX0 (1, 0, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split29A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split30A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split30A0X0Y0_check. -/
theorem X0Split30A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split30A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split30A0X0Y0_pairs. -/
theorem X0Split30A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split30A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split30A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split30A0X0_pairs. -/
theorem X0Split30A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split30A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split30A0_pairs. -/
theorem X0Split30A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split30A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split30_check. -/
theorem X0Split30_check : checkSplit m4TX0 (1, 1, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split30A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split31A0X0Y0Certs : List (Nat × Nat) := [
  (249, 326), (1195, 691), (1680, 766), (2622, 1201), (3454, 1323),
  (3873, 1031), (5271, 396), (5717, 1799), (6308, 1573), (7962, 813),
  (8414, 912), (8792, 1947), (10712, 1394), (11069, 1532), (12489, 1881)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split31A0X0Y0_check. -/
theorem X0Split31A0X0Y0_check : checkGrid m4TX0 1 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split31A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split31A0X0Y0_pairs. -/
theorem X0Split31A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split31A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split31A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split31A0X0_pairs. -/
theorem X0Split31A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split31A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split31A0_pairs. -/
theorem X0Split31A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split31A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split31_check. -/
theorem X0Split31_check : checkSplit m4TX0 (1, 2, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split31A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split32A0X0Y0Certs : List (Nat × Nat) := [
  (106, 391), (172, 642), (1084, 805), (1150, 1112), (1541, 905),
  (1610, 1244), (2647, 160), (2649, 164), (3380, 1381), (3433, 1683),
  (3557, 293), (3842, 1531), (5329, 397), (5332, 408), (5780, 461),
  (5783, 468), (6260, 628), (6513, 1880), (8049, 818), (8053, 835),
  (8506, 919), (8510, 942), (8953, 1001), (8964, 1027), (10781, 1406),
  (10785, 1439), (11228, 1509), (11243, 1566), (12592, 1843), (12609, 1934)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0X0Y0_check. -/
theorem X0Split32A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split32A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0X0Y0_pairs. -/
theorem X0Split32A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split32A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split32A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0X0_pairs. -/
theorem X0Split32A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split32A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0_pairs. -/
theorem X0Split32A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split32A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split32_check. -/
theorem X0Split32_check : checkSplit m4TX0 (1, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split32A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split33A0X0Y0Certs : List (Nat × Nat) := [
  (59, 1816), (131, 215), (171, 785), (287, 497), (301, 10),
  (356, 1351), (473, 993), (484, 53), (515, 72), (657, 1497),
  (669, 153), (700, 192), (795, 386), (826, 453), (892, 894)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0X0Y0_check. -/
theorem X0Split33A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split33A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0X0Y0_pairs. -/
theorem X0Split33A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split33A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split33A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0X0_pairs. -/
theorem X0Split33A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split33A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0_pairs. -/
theorem X0Split33A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split33A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split33_check. -/
theorem X0Split33_check : checkSplit m4TX0 (1, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split33A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split34A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0X0Y0_check. -/
theorem X0Split34A0X0Y0_check : checkGrid m4TX0 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split34A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0X0Y0_pairs. -/
theorem X0Split34A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split34A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split34A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0X0_pairs. -/
theorem X0Split34A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split34A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0_pairs. -/
theorem X0Split34A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split34A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split34_check. -/
theorem X0Split34_check : checkSplit m4TX0 (1, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split34A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split35A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0X0Y0_check. -/
theorem X0Split35A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split35A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0X0Y0_pairs. -/
theorem X0Split35A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split35A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split35A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0X0_pairs. -/
theorem X0Split35A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split35A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0_pairs. -/
theorem X0Split35A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split35A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split35_check. -/
theorem X0Split35_check : checkSplit m4TX0 (2, 0, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split35A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split36A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0X0Y0_check. -/
theorem X0Split36A0X0Y0_check : checkGrid m4TX0 1 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split36A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0X0Y0_pairs. -/
theorem X0Split36A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split36A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split36A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0X0_pairs. -/
theorem X0Split36A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split36A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0_pairs. -/
theorem X0Split36A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split36A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split36_check. -/
theorem X0Split36_check : checkSplit m4TX0 (2, 1, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split36A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split37A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X0Y0_check. -/
theorem X0Split37A0X0Y0_check : checkGrid m4TX0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X0Y0_pairs. -/
theorem X0Split37A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split37A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X0_pairs. -/
theorem X0Split37A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split37A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split37A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X1Y0_check. -/
theorem X0Split37A0X1Y0_check : checkGrid m4TX0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X1Y0_pairs. -/
theorem X0Split37A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split37A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X1_pairs. -/
theorem X0Split37A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split37A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0_pairs. -/
theorem X0Split37A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split37A0X0_pairs x hx y hy hw
  · exact X0Split37A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split37_check. -/
theorem X0Split37_check : checkSplit m4TX0 (2, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split37A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split38A0X0Y0Certs : List (Nat × Nat) := [
  (228, 557), (463, 297), (972, 255), (1200, 0), (1369, 634),
  (1524, 1093), (1983, 39), (2059, 633), (2450, 721), (3018, 560),
  (3422, 22), (3684, 1099), (3903, 33), (4195, 1229), (4438, 1651),
  (4657, 107), (4753, 298), (4794, 1098), (5228, 134), (5365, 1226),
  (5946, 90), (6150, 2), (6342, 258), (6756, 89), (7113, 36),
  (7417, 111), (7828, 1656), (8108, 129), (8504, 343), (8630, 718),
  (8698, 1654), (9240, 6), (9432, 257), (9632, 21), (9919, 635),
  (10117, 110), (10423, 301), (10928, 136), (11234, 342), (11376, 85),
  (11762, 24), (11958, 563), (12535, 1227), (12764, 347), (13010, 719)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0X0Y0_check. -/
theorem X0Split38A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split38A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0X0Y0_pairs. -/
theorem X0Split38A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split38A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split38A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0X0_pairs. -/
theorem X0Split38A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split38A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0_pairs. -/
theorem X0Split38A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split38A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split38_check. -/
theorem X0Split38_check : checkSplit m4TX0 (2, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split38A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split39A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0X0Y0_check. -/
theorem X0Split39A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split39A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0X0Y0_pairs. -/
theorem X0Split39A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split39A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split39A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0X0_pairs. -/
theorem X0Split39A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split39A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0_pairs. -/
theorem X0Split39A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split39A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split39_check. -/
theorem X0Split39_check : checkSplit m4TX0 (2, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split39A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split40A0X0Y0Certs : List (Nat × Nat) := [
  (241, 1684), (501, 1837), (834, 1341), (896, 471), (984, 947),
  (1063, 629), (1214, 412), (1371, 1606), (1454, 244), (1577, 542),
  (1681, 814), (1887, 1332), (2092, 1445), (2110, 1695), (2221, 1045),
  (2330, 1113), (2381, 1597), (2467, 841), (2709, 1075), (2731, 1400),
  (2863, 331), (2984, 1395), (3050, 697), (3152, 1807), (3373, 167),
  (3454, 1968), (3466, 708), (3799, 773), (3895, 1208), (3908, 1922)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X0Y0_check. -/
theorem X0Split40A0X0Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split40A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X0Y0_pairs. -/
theorem X0Split40A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split40A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split40A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X0_pairs. -/
theorem X0Split40A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split40A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0_pairs. -/
theorem X0Split40A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split40A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split40_check. -/
theorem X0Split40_check : checkSplit m4TX0 (3, 0, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split40A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A0X0Y0Certs : List (Nat × Nat) := [
  (901, 0), (4910, 0), (12115, 0), (12127, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0X0Y0_check. -/
theorem X0Split41A0X0Y0_check : checkGrid m4TX0 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0X0Y0_pairs. -/
theorem X0Split41A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split41A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0X0_pairs. -/
theorem X0Split41A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0_pairs. -/
theorem X0Split41A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1X0Y0_check. -/
theorem X0Split41A1X0Y0_check : checkGrid m4TX0 2 91076351 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1X0Y0_pairs. -/
theorem X0Split41A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split41A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1X0_pairs. -/
theorem X0Split41A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1_pairs. -/
theorem X0Split41A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2X0Y0_check. -/
theorem X0Split41A2X0Y0_check : checkGrid m4TX0 2 985062231 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2X0Y0_pairs. -/
theorem X0Split41A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split41A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2X0_pairs. -/
theorem X0Split41A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2_pairs. -/
theorem X0Split41A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3X0Y0_check. -/
theorem X0Split41A3X0Y0_check : checkGrid m4TX0 2 1071345064 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3X0Y0_pairs. -/
theorem X0Split41A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split41A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3X0_pairs. -/
theorem X0Split41A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3_pairs. -/
theorem X0Split41A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split41_check. -/
theorem X0Split41_check : checkSplit m4TX0 (3, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split41A0_pairs x hx y hy hw
    · exact X0Split41A1_pairs x hx y hy hw
    · exact X0Split41A2_pairs x hx y hy hw
    · exact X0Split41A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A0X0Y0Certs : List (Nat × Nat) := [
  (7536, 0), (8457, 0), (9080, 0), (10891, 0), (12265, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0X0Y0_check. -/
theorem X0Split42A0X0Y0_check : checkGrid m4TX0 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0X0Y0_pairs. -/
theorem X0Split42A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0X0_pairs. -/
theorem X0Split42A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0_pairs. -/
theorem X0Split42A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1X0Y0_check. -/
theorem X0Split42A1X0Y0_check : checkGrid m4TX0 2 91076351 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1X0Y0_pairs. -/
theorem X0Split42A1X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1X0_pairs. -/
theorem X0Split42A1X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1_pairs. -/
theorem X0Split42A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2X0Y0_check. -/
theorem X0Split42A2X0Y0_check : checkGrid m4TX0 2 985062231 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2X0Y0_pairs. -/
theorem X0Split42A2X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2X0_pairs. -/
theorem X0Split42A2X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2_pairs. -/
theorem X0Split42A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3X0Y0_check. -/
theorem X0Split42A3X0Y0_check : checkGrid m4TX0 2 1071345064 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3X0Y0_pairs. -/
theorem X0Split42A3X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3X0_pairs. -/
theorem X0Split42A3X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3_pairs. -/
theorem X0Split42A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split42_check. -/
theorem X0Split42_check : checkSplit m4TX0 (3, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split42A0_pairs x hx y hy hw
    · exact X0Split42A1_pairs x hx y hy hw
    · exact X0Split42A2_pairs x hx y hy hw
    · exact X0Split42A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split43A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X0Y0_check. -/
theorem X0Split43A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split43A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X0Y0_pairs. -/
theorem X0Split43A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split43A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split43A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X0_pairs. -/
theorem X0Split43A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split43A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0_pairs. -/
theorem X0Split43A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split43A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split43_check. -/
theorem X0Split43_check : checkSplit m4TX0 (3, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split43A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A0X0Y0Certs : List (Nat × Nat) := [
  (167, 0), (226, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0X0Y0_check. -/
theorem X0Split44A0X0Y0_check : checkGrid m4TX0 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0X0Y0_pairs. -/
theorem X0Split44A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split44A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0X0_pairs. -/
theorem X0Split44A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0_pairs. -/
theorem X0Split44A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1X0Y0_check. -/
theorem X0Split44A1X0Y0_check : checkGrid m4TX0 2 91076351 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1X0Y0_pairs. -/
theorem X0Split44A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split44A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1X0_pairs. -/
theorem X0Split44A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1_pairs. -/
theorem X0Split44A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2X0Y0_check. -/
theorem X0Split44A2X0Y0_check : checkGrid m4TX0 2 985062231 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2X0Y0_pairs. -/
theorem X0Split44A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split44A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2X0_pairs. -/
theorem X0Split44A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2_pairs. -/
theorem X0Split44A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3X0Y0_check. -/
theorem X0Split44A3X0Y0_check : checkGrid m4TX0 2 1071345064 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3X0Y0_pairs. -/
theorem X0Split44A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split44A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3X0_pairs. -/
theorem X0Split44A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3_pairs. -/
theorem X0Split44A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split44_check. -/
theorem X0Split44_check : checkSplit m4TX0 (4, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split44A0_pairs x hx y hy hw
    · exact X0Split44A1_pairs x hx y hy hw
    · exact X0Split44A2_pairs x hx y hy hw
    · exact X0Split44A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0X0Y0_check. -/
theorem X0Split45A0X0Y0_check : checkGrid m4TX0 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0X0Y0_pairs. -/
theorem X0Split45A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split45A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0X0_pairs. -/
theorem X0Split45A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0_pairs. -/
theorem X0Split45A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1X0Y0_check. -/
theorem X0Split45A1X0Y0_check : checkGrid m4TX0 2 91076351 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1X0Y0_pairs. -/
theorem X0Split45A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split45A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1X0_pairs. -/
theorem X0Split45A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1_pairs. -/
theorem X0Split45A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A2X0Y0Certs : List (Nat × Nat) := [
  (740, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2X0Y0_check. -/
theorem X0Split45A2X0Y0_check : checkGrid m4TX0 2 985062231 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2X0Y0_pairs. -/
theorem X0Split45A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split45A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2X0_pairs. -/
theorem X0Split45A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2_pairs. -/
theorem X0Split45A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3X0Y0_check. -/
theorem X0Split45A3X0Y0_check : checkGrid m4TX0 2 1071345064 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3X0Y0_pairs. -/
theorem X0Split45A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split45A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3X0_pairs. -/
theorem X0Split45A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3_pairs. -/
theorem X0Split45A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split45_check. -/
theorem X0Split45_check : checkSplit m4TX0 (4, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split45A0_pairs x hx y hy hw
    · exact X0Split45A1_pairs x hx y hy hw
    · exact X0Split45A2_pairs x hx y hy hw
    · exact X0Split45A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0X0Y0_check. -/
theorem X0Split46A0X0Y0_check : checkGrid m4TX0 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0X0Y0_pairs. -/
theorem X0Split46A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0X0_pairs. -/
theorem X0Split46A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0_pairs. -/
theorem X0Split46A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1X0Y0_check. -/
theorem X0Split46A1X0Y0_check : checkGrid m4TX0 2 91076351 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1X0Y0_pairs. -/
theorem X0Split46A1X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1X0_pairs. -/
theorem X0Split46A1X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1_pairs. -/
theorem X0Split46A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A2X0Y0Certs : List (Nat × Nat) := [
  (25, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2X0Y0_check. -/
theorem X0Split46A2X0Y0_check : checkGrid m4TX0 2 985062231 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2X0Y0_pairs. -/
theorem X0Split46A2X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2X0_pairs. -/
theorem X0Split46A2X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2_pairs. -/
theorem X0Split46A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3X0Y0_check. -/
theorem X0Split46A3X0Y0_check : checkGrid m4TX0 2 1071345064 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3X0Y0_pairs. -/
theorem X0Split46A3X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3X0_pairs. -/
theorem X0Split46A3X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3_pairs. -/
theorem X0Split46A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split46_check. -/
theorem X0Split46_check : checkSplit m4TX0 (4, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split46A0_pairs x hx y hy hw
    · exact X0Split46A1_pairs x hx y hy hw
    · exact X0Split46A2_pairs x hx y hy hw
    · exact X0Split46A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0X0Y0_check. -/
theorem X0Split47A0X0Y0_check : checkGrid m4TX0 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0X0Y0_pairs. -/
theorem X0Split47A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split47A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0X0_pairs. -/
theorem X0Split47A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0_pairs. -/
theorem X0Split47A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1X0Y0_check. -/
theorem X0Split47A1X0Y0_check : checkGrid m4TX0 2 91076351 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1X0Y0_pairs. -/
theorem X0Split47A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split47A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1X0_pairs. -/
theorem X0Split47A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1_pairs. -/
theorem X0Split47A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2X0Y0_check. -/
theorem X0Split47A2X0Y0_check : checkGrid m4TX0 2 985062231 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2X0Y0_pairs. -/
theorem X0Split47A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split47A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2X0_pairs. -/
theorem X0Split47A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2_pairs. -/
theorem X0Split47A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3X0Y0_check. -/
theorem X0Split47A3X0Y0_check : checkGrid m4TX0 2 1071345064 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3X0Y0_pairs. -/
theorem X0Split47A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split47A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3X0_pairs. -/
theorem X0Split47A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3_pairs. -/
theorem X0Split47A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split47_check. -/
theorem X0Split47_check : checkSplit m4TX0 (5, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split47A0_pairs x hx y hy hw
    · exact X0Split47A1_pairs x hx y hy hw
    · exact X0Split47A2_pairs x hx y hy hw
    · exact X0Split47A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split48A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A0X0Y0_check. -/
theorem X0Split48A0X0Y0_check : checkGrid m4TX0 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A0X0Y0_pairs. -/
theorem X0Split48A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split48A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A0X0_pairs. -/
theorem X0Split48A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split48A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A0_pairs. -/
theorem X0Split48A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split48A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split48A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A1X0Y0_check. -/
theorem X0Split48A1X0Y0_check : checkGrid m4TX0 2 91076351 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A1X0Y0_pairs. -/
theorem X0Split48A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split48A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A1X0_pairs. -/
theorem X0Split48A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split48A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A1_pairs. -/
theorem X0Split48A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split48A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split48A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A2X0Y0_check. -/
theorem X0Split48A2X0Y0_check : checkGrid m4TX0 2 985062231 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A2X0Y0_pairs. -/
theorem X0Split48A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split48A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A2X0_pairs. -/
theorem X0Split48A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split48A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A2_pairs. -/
theorem X0Split48A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split48A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split48A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A3X0Y0_check. -/
theorem X0Split48A3X0Y0_check : checkGrid m4TX0 2 1071345064 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A3X0Y0_pairs. -/
theorem X0Split48A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split48A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split48A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A3X0_pairs. -/
theorem X0Split48A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split48A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48A3_pairs. -/
theorem X0Split48A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split48A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split48_check. -/
theorem X0Split48_check : checkSplit m4TX0 (5, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split48A0_pairs x hx y hy hw
    · exact X0Split48A1_pairs x hx y hy hw
    · exact X0Split48A2_pairs x hx y hy hw
    · exact X0Split48A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split49A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A0X0Y0_check. -/
theorem X0Split49A0X0Y0_check : checkGrid m4TX0 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A0X0Y0_pairs. -/
theorem X0Split49A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split49A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A0X0_pairs. -/
theorem X0Split49A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split49A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A0_pairs. -/
theorem X0Split49A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split49A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split49A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A1X0Y0_check. -/
theorem X0Split49A1X0Y0_check : checkGrid m4TX0 2 91076351 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A1X0Y0_pairs. -/
theorem X0Split49A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split49A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A1X0_pairs. -/
theorem X0Split49A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split49A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A1_pairs. -/
theorem X0Split49A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split49A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split49A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A2X0Y0_check. -/
theorem X0Split49A2X0Y0_check : checkGrid m4TX0 2 985062231 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A2X0Y0_pairs. -/
theorem X0Split49A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split49A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A2X0_pairs. -/
theorem X0Split49A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split49A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A2_pairs. -/
theorem X0Split49A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split49A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split49A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A3X0Y0_check. -/
theorem X0Split49A3X0Y0_check : checkGrid m4TX0 2 1071345064 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A3X0Y0_pairs. -/
theorem X0Split49A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split49A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split49A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A3X0_pairs. -/
theorem X0Split49A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split49A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49A3_pairs. -/
theorem X0Split49A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split49A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split49_check. -/
theorem X0Split49_check : checkSplit m4TX0 (6, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split49A0_pairs x hx y hy hw
    · exact X0Split49A1_pairs x hx y hy hw
    · exact X0Split49A2_pairs x hx y hy hw
    · exact X0Split49A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split50A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split50A0X0Y0_check. -/
theorem X0Split50A0X0Y0_check : checkGrid m4TX0 1 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split50A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split50A0X0Y0_pairs. -/
theorem X0Split50A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 8 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split50A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split50A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split50A0X0_pairs. -/
theorem X0Split50A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 8 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split50A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split50A0_pairs. -/
theorem X0Split50A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 8 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split50A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split50_check. -/
theorem X0Split50_check : checkSplit m4TX0 (0, 0, 8, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split50A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split51A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split51A0X0Y0_check. -/
theorem X0Split51A0X0Y0_check : checkGrid m4TX0 1 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split51A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split51A0X0Y0_pairs. -/
theorem X0Split51A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 7 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split51A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split51A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split51A0X0_pairs. -/
theorem X0Split51A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 7 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split51A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split51A0_pairs. -/
theorem X0Split51A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 7 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split51A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split51_check. -/
theorem X0Split51_check : checkSplit m4TX0 (0, 1, 7, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split51A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split52A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split52A0X0Y0_check. -/
theorem X0Split52A0X0Y0_check : checkGrid m4TX0 1 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split52A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split52A0X0Y0_pairs. -/
theorem X0Split52A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split52A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split52A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split52A0X0_pairs. -/
theorem X0Split52A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split52A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split52A0_pairs. -/
theorem X0Split52A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split52A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split52_check. -/
theorem X0Split52_check : checkSplit m4TX0 (0, 2, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split52A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split53A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split53A0X0Y0_check. -/
theorem X0Split53A0X0Y0_check : checkGrid m4TX0 1 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split53A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split53A0X0Y0_pairs. -/
theorem X0Split53A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split53A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X0Split53A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split53A0X0_pairs. -/
theorem X0Split53A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split53A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split53A0_pairs. -/
theorem X0Split53A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split53A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split53_check. -/
theorem X0Split53_check : checkSplit m4TX0 (0, 3, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split53A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split54A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split54A0X0Y0_check. -/
theorem X0Split54A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split54A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split54A0X0Y0_pairs. -/
theorem X0Split54A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split54A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S256Chunk0 masks4S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · exact X0Split54A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split54A0X0_pairs. -/
theorem X0Split54A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split54A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split54A0_pairs. -/
theorem X0Split54A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split54A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split54_check. -/
theorem X0Split54_check : checkSplit m4TX0 (0, 4, 4, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split54A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split55A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split55A0X0Y0_check. -/
theorem X0Split55A0X0Y0_check : checkGrid m4TX0 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split55A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split55A0X0Y0_pairs. -/
theorem X0Split55A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split55A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X0Split55A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split55A0X0_pairs. -/
theorem X0Split55A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split55A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split55A0_pairs. -/
theorem X0Split55A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split55A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split55_check. -/
theorem X0Split55_check : checkSplit m4TX0 (0, 5, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split55A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split56A0X0Y0Certs : List (Nat × Nat) := [
  (4, 41), (25, 123), (33, 139), (55, 227), (87, 324),
  (101, 366), (138, 509), (186, 688), (206, 763), (259, 1011),
  (297, 1192), (322, 1318), (363, 1539), (404, 1787), (424, 1893)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split56A0X0Y0_check. -/
theorem X0Split56A0X0Y0_check : checkGrid m4TX0 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split56A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split56A0X0Y0_pairs. -/
theorem X0Split56A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split56A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split56A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split56A0X0_pairs. -/
theorem X0Split56A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split56A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split56A0_pairs. -/
theorem X0Split56A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split56A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split56_check. -/
theorem X0Split56_check : checkSplit m4TX0 (0, 6, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split56A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split57A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split57A0X0Y0_check. -/
theorem X0Split57A0X0Y0_check : checkGrid m4TX0 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split57A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split57A0X0Y0_pairs. -/
theorem X0Split57A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split57A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split57A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split57A0X0_pairs. -/
theorem X0Split57A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split57A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split57A0_pairs. -/
theorem X0Split57A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split57A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split57_check. -/
theorem X0Split57_check : checkSplit m4TX0 (0, 7, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split57A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split58A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split58A0X0Y0_check. -/
theorem X0Split58A0X0Y0_check : checkGrid m4TX0 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split58A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split58A0X0Y0_pairs. -/
theorem X0Split58A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 8 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split58A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split58A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split58A0X0_pairs. -/
theorem X0Split58A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 8 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split58A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split58A0_pairs. -/
theorem X0Split58A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 8 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split58A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split58_check. -/
theorem X0Split58_check : checkSplit m4TX0 (0, 8, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split58A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split59A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split59A0X0Y0_check. -/
theorem X0Split59A0X0Y0_check : checkGrid m4TX0 1 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split59A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split59A0X0Y0_pairs. -/
theorem X0Split59A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 7 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split59A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split59A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split59A0X0_pairs. -/
theorem X0Split59A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 7 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split59A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split59A0_pairs. -/
theorem X0Split59A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 7 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split59A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split59_check. -/
theorem X0Split59_check : checkSplit m4TX0 (1, 0, 7, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split59A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split60A0X0Y0Certs : List (Nat × Nat) := [
  (6, 1188), (49, 1992), (72, 1310), (103, 1768), (144, 1166),
  (175, 1316), (198, 1776), (229, 1149), (260, 1781), (273, 714),
  (328, 1771), (342, 1491), (360, 1722), (414, 712), (445, 1742),
  (457, 1222), (488, 1343), (528, 1779), (542, 684), (573, 1187),
  (628, 1345), (643, 1640), (674, 1706), (690, 1694), (727, 1298),
  (758, 1770), (800, 762), (812, 626), (854, 1306), (876, 983)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split60A0X0Y0_check. -/
theorem X0Split60A0X0Y0_check : checkGrid m4TX0 1 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split60A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split60A0X0Y0_pairs. -/
theorem X0Split60A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split60A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split60A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split60A0X0_pairs. -/
theorem X0Split60A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split60A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split60A0_pairs. -/
theorem X0Split60A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split60A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split60_check. -/
theorem X0Split60_check : checkSplit m4TX0 (1, 1, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split60A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split61A0X0Y0Certs : List (Nat × Nat) := [
  (171, 1165), (820, 1993), (1148, 622), (1608, 1769), (1826, 1634),
  (2342, 1315), (2628, 931), (3430, 1220), (3554, 1780), (4100, 1906),
  (4540, 1739), (5063, 1476), (5293, 1425), (5741, 1590), (6257, 1736),
  (6821, 1223), (7262, 1311), (7413, 967), (7996, 668), (8450, 1960),
  (8890, 1274), (9438, 1641), (9954, 1705), (10078, 1388), (10736, 1299),
  (11177, 1752), (11384, 761), (11911, 625), (12564, 1305), (12786, 972)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split61A0X0Y0_check. -/
theorem X0Split61A0X0Y0_check : checkGrid m4TX0 1 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split61A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split61A0X0Y0_pairs. -/
theorem X0Split61A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split61A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split61A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split61A0X0_pairs. -/
theorem X0Split61A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split61A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split61A0_pairs. -/
theorem X0Split61A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split61A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split61_check. -/
theorem X0Split61_check : checkSplit m4TX0 (1, 2, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split61A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split62A0X0Y0Certs : List (Nat × Nat) := [
  (957, 1203), (4708, 706), (5609, 1946), (9936, 690), (14263, 1801),
  (17967, 1221), (18883, 1629), (22278, 1252), (23278, 823), (27407, 1198),
  (29139, 1322), (35802, 1948), (37078, 1986), (39438, 1639), (43848, 1704),
  (44388, 434), (44763, 291), (45445, 1416), (52611, 327), (54663, 1796),
  (57432, 1545), (62411, 1949), (63513, 1991), (66701, 874), (69019, 760),
  (69550, 624), (71003, 982), (75757, 692), (80288, 767), (82840, 1905),
  (85406, 1147), (87405, 1572), (92237, 1202), (93037, 1314), (94878, 971),
  (96321, 1490), (101266, 1324), (104305, 1032), (106342, 1733), (109094, 399),
  (110950, 1475), (113344, 1800), (116195, 1574), (117746, 584), (118620, 923)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split62A0X0Y0_check. -/
theorem X0Split62A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split62A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split62A0X0Y0_pairs. -/
theorem X0Split62A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split62A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks1S256Chunk0 masks3S4096Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact X0Split62A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split62A0X0_pairs. -/
theorem X0Split62A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split62A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split62A0_pairs. -/
theorem X0Split62A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split62A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split62_check. -/
theorem X0Split62_check : checkSplit m4TX0 (1, 3, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split62A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split63A0X0Y0Certs : List (Nat × Nat) := [
  (464, 398), (993, 654), (2253, 1206), (3294, 1670), (7973, 1939),
  (8375, 285), (9493, 822), (10148, 1110), (10229, 1143), (13082, 609),
  (13773, 922), (14579, 1266), (15806, 1803), (19242, 1544), (21717, 840),
  (24404, 124), (24894, 431), (25280, 615), (25410, 673), (29480, 679),
  (31154, 1415), (31729, 1679), (31900, 1738), (32701, 267), (34694, 1179),
  (35541, 1567), (36299, 1901), (40364, 1904), (41675, 689), (47466, 1444),
  (49049, 329), (50031, 782), (50225, 869), (50922, 1172), (53197, 369),
  (54515, 977), (54996, 1180), (55278, 1304), (57673, 581), (57711, 595),
  (59145, 1240), (60749, 1937), (62726, 1028), (67198, 1197), (71556, 1321),
  (74167, 695), (75141, 1128), (75185, 1141), (75658, 1340), (78414, 770),
  (79458, 1246), (80050, 1481), (80730, 1778), (81435, 276), (81881, 511),
  (84186, 1535), (84503, 1675), (88323, 1568), (89408, 166), (96991, 1795),
  (99991, 1328), (100789, 1692), (100841, 1714), (100914, 1735), (101860, 339),
  (102384, 602), (103288, 1015), (105302, 1889), (106040, 411), (110213, 470),
  (114511, 579), (114816, 710), (115615, 1071), (116677, 1542), (119381, 946)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split63A0X0Y0_check. -/
theorem X0Split63A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split63A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split63A0X0Y0_pairs. -/
theorem X0Split63A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split63A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S256Chunk0 masks3S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact X0Split63A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split63A0X0_pairs. -/
theorem X0Split63A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split63A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split63A0_pairs. -/
theorem X0Split63A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split63A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split63_check. -/
theorem X0Split63_check : checkSplit m4TX0 (1, 4, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split63A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split64A0X0Y0Certs : List (Nat × Nat) := [
  (167, 613), (174, 644), (580, 530), (588, 567), (599, 593),
  (798, 1538), (868, 1983), (1060, 724), (1153, 1120), (1583, 1106),
  (1613, 1249), (1741, 30), (1876, 505), (2008, 1050), (2157, 1856),
  (2164, 1891), (2299, 458), (2361, 687), (2400, 846), (2452, 1102),
  (2454, 1109), (2691, 306), (2912, 1235), (3063, 101), (3437, 1700),
  (3546, 262), (3865, 1672), (3932, 96), (3970, 226), (4062, 535),
  (4170, 1004), (4287, 1605), (4359, 64), (4374, 119), (4561, 800),
  (4590, 914), (4647, 1190), (5048, 1023), (5107, 1319), (5132, 1450),
  (5168, 1665), (5171, 1678), (5398, 653), (5604, 1669), (5728, 278),
  (5853, 736), (6176, 321), (6245, 571), (6597, 275), (6663, 508),
  (6795, 1062), (6882, 1516), (6932, 1833), (6964, 40), (6967, 62),
  (7003, 175), (7045, 314), (7300, 1398), (7448, 209), (7494, 362),
  (7725, 1369), (7762, 1555), (7799, 1786), (7904, 282), (8119, 1140),
  (8431, 606), (8579, 1265), (8715, 92), (8885, 676), (9194, 237),
  (9300, 599), (9394, 1012), (9509, 1624), (9553, 1858), (9595, 122),
  (9610, 168), (9688, 429), (9754, 670), (9785, 808), (10038, 140),
  (10055, 202), (10139, 485), (10209, 754), (10433, 1919), (10611, 639),
  (10838, 1731), (10943, 266), (11171, 1178), (11356, 193), (11397, 325),
  (11424, 415), (11539, 867), (11605, 1168), (11846, 367), (11875, 473),
  (11996, 975), (12065, 1302), (12081, 1385), (12339, 577), (12483, 1237),
  (12756, 515), (12821, 765), (12862, 950), (12965, 1479), (13018, 1774)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0X0Y0_check. -/
theorem X0Split64A0X0Y0_check : checkGrid m4TX0 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0X0Y0_pairs. -/
theorem X0Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split64A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0X0_pairs. -/
theorem X0Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0_pairs. -/
theorem X0Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split64_check. -/
theorem X0Split64_check : checkSplit m4TX0 (1, 5, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split65A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0X0Y0_check. -/
theorem X0Split65A0X0Y0_check : checkGrid m4TX0 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0X0Y0_pairs. -/
theorem X0Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split65A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0X0_pairs. -/
theorem X0Split65A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0_pairs. -/
theorem X0Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split65_check. -/
theorem X0Split65_check : checkSplit m4TX0 (1, 6, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0X0Y0_check. -/
theorem X0Split66A0X0Y0_check : checkGrid m4TX0 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0X0Y0_pairs. -/
theorem X0Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split66A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0X0_pairs. -/
theorem X0Split66A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0_pairs. -/
theorem X0Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split66_check. -/
theorem X0Split66_check : checkSplit m4TX0 (1, 7, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split67A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0X0Y0_check. -/
theorem X0Split67A0X0Y0_check : checkGrid m4TX0 1 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0X0Y0_pairs. -/
theorem X0Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split67A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0X0_pairs. -/
theorem X0Split67A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0_pairs. -/
theorem X0Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split67_check. -/
theorem X0Split67_check : checkSplit m4TX0 (2, 0, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split67A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split68A0X0Y0Certs : List (Nat × Nat) := [
  (493, 1297), (1347, 815), (1852, 1613), (2119, 1766), (2134, 1815),
  (2397, 1453), (2510, 1186), (3153, 1867), (3257, 1565), (3599, 334),
  (3615, 1396), (4466, 1915), (4884, 1637), (4899, 1961), (5279, 1449),
  (5455, 1327), (5470, 1973), (5865, 1987), (6036, 1765), (6367, 751),
  (6533, 1933), (6911, 702), (7011, 776), (7028, 839), (7174, 1092),
  (7702, 1884), (8135, 1060), (8561, 1026), (8788, 1798), (8806, 1811),
  (9047, 1214), (9321, 1978), (9522, 1635), (9931, 1338), (9974, 683),
  (10179, 1650), (10540, 1622), (10766, 1046), (10770, 1442), (11483, 1426),
  (11821, 556), (12048, 1930), (12256, 1980), (12575, 1601), (12602, 1286)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0X0Y0_check. -/
theorem X0Split68A0X0Y0_check : checkGrid m4TX0 1 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0X0Y0_pairs. -/
theorem X0Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split68A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0X0_pairs. -/
theorem X0Split68A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0_pairs. -/
theorem X0Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split68_check. -/
theorem X0Split68_check : checkSplit m4TX0 (2, 1, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split68A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split69A0X0Y0Certs : List (Nat × Nat) := [
  (1924, 1956), (2374, 1467), (5475, 988), (6674, 376), (9186, 1710),
  (11170, 597), (12060, 1608), (13244, 1632), (13924, 1726), (14675, 1751),
  (15351, 1923), (19265, 821), (19608, 1294), (22542, 1462), (23997, 1488),
  (26741, 1025), (27013, 1647), (29119, 1785), (29852, 783), (31247, 1591),
  (34624, 555), (34932, 853), (35429, 744), (38124, 540), (39549, 1859),
  (39851, 1614), (40154, 1873), (41039, 969), (42504, 1886), (43525, 1148),
  (44338, 1145), (45483, 1404), (47035, 1921), (52006, 420), (52464, 1412),
  (53171, 1741), (57838, 1561), (60195, 1734), (60520, 1185), (64702, 1564),
  (64933, 1887), (67487, 1794), (67872, 1312), (69134, 749), (69540, 1346),
  (70178, 1053), (71328, 1962), (75908, 1581), (76488, 1091), (77244, 945),
  (77739, 1283), (79276, 1335), (80934, 1072), (82244, 623), (83890, 1931),
  (84641, 857), (84912, 1059), (85967, 1461), (86181, 127), (88263, 1056),
  (89262, 711), (89996, 681), (91258, 875), (94533, 1387), (94883, 1609),
  (100391, 851), (101723, 958), (103301, 1342), (103969, 1611), (108479, 1927)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X0Y0_check. -/
theorem X0Split69A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X0Y0_pairs. -/
theorem X0Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X0_pairs. -/
theorem X0Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split69A0X1Y0Certs : List (Nat × Nat) := [
  (37, 1940), (1458, 1259), (1878, 1288), (6929, 1932), (7189, 1057),
  (8795, 960), (11837, 1902), (12242, 1414), (13039, 1649), (13909, 682),
  (14245, 1443), (14748, 1762), (16309, 1812), (17920, 1587), (19811, 932),
  (22180, 1482), (22945, 1175), (23405, 961), (23676, 1621), (25170, 1560),
  (25362, 338), (27188, 1617), (28461, 1183), (28809, 1184), (29590, 1219),
  (30151, 1417), (33054, 1465), (35557, 1702), (36130, 1888), (41358, 1403),
  (44479, 1549), (46546, 1718), (47239, 1693), (52042, 1618), (53162, 1950),
  (53802, 1262), (54422, 1557), (55145, 1427), (58348, 1721), (59172, 1196),
  (59978, 1468), (60327, 1979), (61744, 1926), (62019, 709), (64584, 1273),
  (66221, 860), (66564, 1951), (71124, 1911), (73097, 980), (73878, 610)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X1Y0_check. -/
theorem X0Split69A0X1Y0_check : checkGrid m4TX0 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X1Y0_pairs. -/
theorem X0Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X1_pairs. -/
theorem X0Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0_pairs. -/
theorem X0Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split69A0X0_pairs x hx y hy hw
  · exact X0Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split69_check. -/
theorem X0Split69_check : checkSplit m4TX0 (2, 2, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split69A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y0Certs : List (Nat × Nat) := [
  (8132, 377), (39389, 410), (51701, 418), (72799, 172), (78151, 328),
  (79442, 146), (80859, 407), (101430, 128), (114417, 281), (116403, 240),
  (127074, 173)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y0_check. -/
theorem X0Split70A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y0_pairs. -/
theorem X0Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X0Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y1Certs : List (Nat × Nat) := [
  (21284, 554), (31748, 426), (42092, 478), (55209, 621), (57666, 582),
  (88448, 608), (99878, 437), (107286, 550), (110588, 664), (118766, 659),
  (130270, 532)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y1_check. -/
theorem X0Split70A0X0Y1_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y1_pairs. -/
theorem X0Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X0Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y2Certs : List (Nat × Nat) := [
  (7612, 859), (10585, 819), (16731, 820), (18814, 834), (21445, 862),
  (35119, 784), (41726, 772), (76742, 863), (86916, 837), (87230, 748),
  (105390, 848), (112049, 852)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y2_check. -/
theorem X0Split70A0X0Y2_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y2_pairs. -/
theorem X0Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X0Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y3Certs : List (Nat × Nat) := [
  (14274, 1084), (27899, 1014), (31283, 921), (47187, 936), (58168, 1038),
  (59252, 1065), (59355, 1090), (62609, 956), (63648, 966), (67356, 1024),
  (82777, 1052), (92310, 962), (96356, 944), (102691, 1029), (110602, 904),
  (111397, 1030), (127636, 959)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y3_check. -/
theorem X0Split70A0X0Y3_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y3_pairs. -/
theorem X0Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X0Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y4Certs : List (Nat × Nat) := [
  (20012, 1136), (23660, 1161), (30622, 1289), (91647, 1330), (122090, 1218),
  (125502, 1144), (129955, 1292)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y4_check. -/
theorem X0Split70A0X0Y4_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y4_pairs. -/
theorem X0Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X0Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y5Certs : List (Nat × Nat) := [
  (2751, 1421), (23211, 1411), (29438, 1447), (33345, 1373), (34382, 1380),
  (40956, 1571), (45736, 1410), (46491, 1529), (53352, 1386), (59707, 1472),
  (63204, 1436), (67119, 1366), (69555, 1540), (75942, 1409), (81446, 1347),
  (99543, 1431), (113550, 1522), (121647, 1460), (122941, 1372), (127470, 1562)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y5_check. -/
theorem X0Split70A0X0Y5_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y5_pairs. -/
theorem X0Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X0Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y6Certs : List (Nat × Nat) := [
  (6192, 1598), (39725, 1701), (46665, 1610), (65918, 1724), (67919, 1717),
  (72668, 1764), (74549, 1708), (109145, 1620), (114711, 1582), (115822, 1627),
  (115905, 1648), (116407, 1646), (122786, 1744)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y6_check. -/
theorem X0Split70A0X0Y6_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y6_pairs. -/
theorem X0Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X0Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y7Certs : List (Nat × Nat) := [
  (10877, 1977), (16965, 1920), (24656, 1969), (31436, 1790), (45993, 1914),
  (51771, 1957), (55612, 1976), (65383, 1868), (66488, 1936), (75519, 1924),
  (83055, 1897), (83636, 1944), (83973, 1879), (90158, 1878), (91239, 1935),
  (91583, 1877), (110717, 1913), (110862, 1984), (120184, 1898), (121024, 1852)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y7_check. -/
theorem X0Split70A0X0Y7_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y7_pairs. -/
theorem X0Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X0Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0_pairs. -/
theorem X0Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split70A0X0Y0_pairs x hx y hy hw
  · exact X0Split70A0X0Y1_pairs x hx y hy hw
  · exact X0Split70A0X0Y2_pairs x hx y hy hw
  · exact X0Split70A0X0Y3_pairs x hx y hy hw
  · exact X0Split70A0X0Y4_pairs x hx y hy hw
  · exact X0Split70A0X0Y5_pairs x hx y hy hw
  · exact X0Split70A0X0Y6_pairs x hx y hy hw
  · exact X0Split70A0X0Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y0Certs : List (Nat × Nat) := [
  (5112, 422), (14243, 371), (30057, 340), (36350, 424), (37587, 253),
  (42609, 179), (43306, 312), (47613, 423), (59772, 358), (69635, 44),
  (70647, 421)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y0_check. -/
theorem X0Split70A0X1Y0_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y0_pairs. -/
theorem X0Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X0Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y1Certs : List (Nat × Nat) := [
  (12760, 651), (50801, 479), (77882, 462), (82099, 517), (87321, 551)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y1_check. -/
theorem X0Split70A0X1Y1_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y1_pairs. -/
theorem X0Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X0Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y2Certs : List (Nat × Nat) := [
  (759, 768), (6480, 817), (9788, 693), (28153, 879), (45607, 680),
  (51641, 858), (58291, 854), (72817, 713), (77498, 746), (88242, 745)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y2_check. -/
theorem X0Split70A0X1Y2_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y2_pairs. -/
theorem X0Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X0Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y3Certs : List (Nat × Nat) := [
  (7755, 930), (8581, 1070), (10308, 927), (15453, 940), (25663, 926),
  (28619, 1086), (33321, 916), (35271, 1085), (51058, 1061), (76910, 949),
  (79368, 901), (81564, 964), (82135, 986), (86879, 1054)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y3_check. -/
theorem X0Split70A0X1Y3_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y3_pairs. -/
theorem X0Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X0Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y4Certs : List (Nat × Nat) := [
  (25261, 1182), (26810, 1193), (27153, 1130), (36437, 1155), (41361, 1285),
  (50553, 1279), (53748, 1325), (62154, 1204), (67917, 1261), (71014, 1268),
  (80154, 1251)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y4_check. -/
theorem X0Split70A0X1Y4_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y4_pairs. -/
theorem X0Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X0Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y5Certs : List (Nat × Nat) := [
  (2472, 1534), (18229, 1469), (22256, 1440), (24998, 1533), (31225, 1569),
  (35635, 1466), (39905, 1551), (41962, 1558), (42397, 1530), (48843, 1424),
  (51461, 1448), (61299, 1513), (63125, 1401), (64486, 1556), (68793, 1420)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y5_check. -/
theorem X0Split70A0X1Y5_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y5_pairs. -/
theorem X0Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X0Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y6Certs : List (Nat × Nat) := [
  (3721, 1631), (14883, 1588), (15952, 1615), (50058, 1732), (56076, 1690),
  (71212, 1596), (80829, 1757), (81513, 1623)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y6_check. -/
theorem X0Split70A0X1Y6_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y6_pairs. -/
theorem X0Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X0Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y7Certs : List (Nat × Nat) := [
  (2754, 1967), (15763, 1805), (34934, 1874), (44108, 1928), (51623, 1885),
  (53000, 1866), (62568, 1882), (68876, 1941), (72936, 1849), (78580, 1802)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y7_check. -/
theorem X0Split70A0X1Y7_check : checkGrid m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y7_pairs. -/
theorem X0Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X0Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1_pairs. -/
theorem X0Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split70A0X1Y0_pairs x hx y hy hw
  · exact X0Split70A0X1Y1_pairs x hx y hy hw
  · exact X0Split70A0X1Y2_pairs x hx y hy hw
  · exact X0Split70A0X1Y3_pairs x hx y hy hw
  · exact X0Split70A0X1Y4_pairs x hx y hy hw
  · exact X0Split70A0X1Y5_pairs x hx y hy hw
  · exact X0Split70A0X1Y6_pairs x hx y hy hw
  · exact X0Split70A0X1Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0_pairs. -/
theorem X0Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split70A0X0_pairs x hx y hy hw
  · exact X0Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split70_check. -/
theorem X0Split70_check : checkSplit m4TX0 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split71A0X0Y0Certs : List (Nat × Nat) := [
  (239, 910), (609, 645), (3451, 1828), (3462, 1854), (3819, 1390),
  (6006, 1506), (6306, 809), (6364, 1083), (6705, 657), (7678, 1121),
  (7842, 80), (8985, 1125), (10748, 1250), (14179, 1013), (14353, 1981),
  (16243, 538), (16248, 566), (17457, 231), (17547, 534), (18045, 797),
  (18465, 731), (19662, 323), (19800, 844), (21961, 798), (21963, 802),
  (23028, 1834), (23557, 264), (23842, 1508), (27513, 395), (28609, 1379),
  (28613, 1389), (28732, 116), (29871, 1154), (31401, 307), (31806, 205),
  (32583, 1707), (33168, 393), (35551, 1275), (37367, 1699), (37472, 246),
  (39109, 1711), (43131, 263), (43863, 1537), (43917, 1855), (46182, 274),
  (46518, 1835), (47416, 29), (47686, 1068), (49216, 243), (49732, 519),
  (49860, 1063), (50027, 31), (50783, 1329), (51205, 1257), (53256, 686),
  (53281, 799), (54550, 648), (54654, 1108), (56557, 61), (56572, 115),
  (57313, 1365), (57916, 241), (58882, 574), (59135, 1840), (60017, 1876),
  (60021, 1907), (60671, 764), (60812, 1451), (64275, 1368), (64278, 1374),
  (65467, 810), (66230, 401), (66296, 650), (66844, 1139), (67507, 308),
  (68755, 121), (68844, 417), (69378, 804), (71953, 652), (72342, 480),
  (72863, 816), (73732, 811), (74634, 965), (75786, 357), (77830, 1754),
  (80238, 735), (80624, 544), (82019, 909), (82742, 350), (83356, 1067),
  (86395, 1033), (88895, 572), (89322, 533), (89599, 1892), (92154, 1575),
  (92218, 1982), (93151, 242), (93255, 600), (95282, 97), (95616, 1504),
  (96496, 1527), (96500, 1546), (97588, 537), (98140, 1035), (98249, 1625),
  (98329, 102), (99150, 1804), (99574, 1713), (100564, 304), (100995, 286),
  (102844, 671), (102877, 812), (103102, 60), (103392, 1191), (104859, 118),
  (105120, 1127), (107485, 169), (107527, 310), (107906, 125), (108898, 539),
  (109656, 159), (109684, 249), (110904, 1847)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X0Y0_check. -/
theorem X0Split71A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X0Y0_pairs. -/
theorem X0Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X0_pairs. -/
theorem X0Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split71A0X1Y0Certs : List (Nat × Nat) := [
  (677, 925), (746, 1260), (2062, 1317), (2070, 1367), (3790, 1256),
  (3866, 1676), (6140, 204), (6186, 355), (7474, 303), (8485, 826),
  (8551, 1132), (9895, 1360), (10403, 1730), (11945, 740), (13586, 365),
  (13732, 952), (14688, 1375), (17279, 1264), (17672, 1077), (19044, 1392),
  (20204, 730), (20820, 1630), (21231, 1505), (22677, 233), (25599, 1577),
  (27855, 93), (28330, 228), (28545, 1064), (30557, 392), (30601, 548),
  (31060, 647), (31923, 616), (32415, 845), (32481, 1152), (34444, 305),
  (34660, 1169), (35239, 42), (35275, 170), (37060, 315), (37083, 394),
  (39699, 416), (39765, 658), (40108, 330), (40726, 1069), (42825, 733),
  (43167, 370), (43687, 696), (45582, 1419), (45635, 1719), (46430, 1300),
  (46449, 1391), (47030, 203), (47384, 1788), (48819, 360), (49114, 1712),
  (51460, 474), (51530, 741), (52375, 646), (52756, 455), (52758, 457),
  (53643, 510), (53879, 1626), (55989, 1253), (56524, 1838), (56709, 578),
  (57393, 1836), (59302, 518), (62176, 1830), (64013, 265), (67660, 902),
  (67663, 907), (68605, 1255), (69372, 771), (69898, 1207), (70382, 1452),
  (70435, 1753), (72033, 1009), (72036, 1016), (72840, 732), (73048, 1772),
  (73548, 141), (73645, 475), (75459, 752), (75494, 908), (77242, 951),
  (77311, 1276), (77715, 1126)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X1Y0_check. -/
theorem X0Split71A0X1Y0_check : checkGrid m4TX0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X1Y0_pairs. -/
theorem X0Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X1_pairs. -/
theorem X0Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0_pairs. -/
theorem X0Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split71A0X0_pairs x hx y hy hw
  · exact X0Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split71_check. -/
theorem X0Split71_check : checkSplit m4TX0 (2, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split72A0X0Y0Certs : List (Nat × Nat) := [
  (364, 45), (987, 1502), (1139, 1818), (1365, 387), (1382, 23),
  (1539, 148), (1784, 348), (1870, 183), (2777, 492), (3029, 1819),
  (3203, 999), (3281, 220), (3681, 793), (3726, 88), (3771, 791),
  (3975, 383), (4192, 892), (4237, 113), (4370, 717), (4486, 445),
  (4749, 154), (5843, 990), (6161, 217), (6447, 1492), (6450, 7),
  (6551, 224), (6587, 500), (7089, 158), (7111, 15), (7212, 261),
  (7231, 17), (7491, 795), (7826, 1358), (7903, 295), (7946, 1348),
  (8065, 1228), (8182, 891), (8626, 446), (9297, 1495), (9647, 498),
  (9751, 19), (10065, 381), (10083, 35), (10114, 54), (10218, 564),
  (10234, 56), (10876, 448), (10925, 75), (11029, 631), (11045, 67),
  (11188, 1655), (11276, 1359), (11393, 996), (11819, 1824), (12218, 135),
  (12275, 77), (12712, 885), (12760, 184), (12864, 1095), (12880, 186)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0X0Y0_check. -/
theorem X0Split72A0X0Y0_check : checkGrid m4TX0 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0X0Y0_pairs. -/
theorem X0Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split72A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0X0_pairs. -/
theorem X0Split72A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0_pairs. -/
theorem X0Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split72_check. -/
theorem X0Split72_check : checkSplit m4TX0 (2, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0X0Y0_check. -/
theorem X0Split73A0X0Y0_check : checkGrid m4TX0 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0X0Y0_pairs. -/
theorem X0Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split73A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0X0_pairs. -/
theorem X0Split73A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0_pairs. -/
theorem X0Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split73_check. -/
theorem X0Split73_check : checkSplit m4TX0 (2, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split74A0X0Y0Certs : List (Nat × Nat) := [
  (214, 1296), (694, 1809), (726, 1213), (809, 1750), (1390, 1435),
  (1825, 1959), (1895, 1487), (2017, 1131), (2656, 1972), (3060, 1074),
  (3165, 1716), (3271, 438), (3665, 881), (3906, 1600), (3994, 939)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X0Y0_check. -/
theorem X0Split74A0X0Y0_check : checkGrid m4TX0 1 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X0Y0_pairs. -/
theorem X0Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split74A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X0_pairs. -/
theorem X0Split74A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0_pairs. -/
theorem X0Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split74A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split74_check. -/
theorem X0Split74_check : checkSplit m4TX0 (3, 0, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split74A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split75A0X0Y0Certs : List (Nat × Nat) := [
  (3603, 359), (4149, 1971), (4792, 1137), (5431, 1925), (5726, 1459),
  (5910, 756), (8915, 1616), (12329, 1864), (17047, 747), (19005, 1797),
  (20186, 583), (20781, 884), (20798, 322), (22504, 1413), (22996, 1612),
  (23015, 1543), (23402, 1307), (24267, 1725), (27257, 1209), (28599, 1910),
  (30550, 1945), (34403, 1434), (36011, 1405), (37931, 703), (40917, 1520),
  (42131, 698), (42214, 1806), (44664, 1124), (47473, 1291), (49462, 1958),
  (51201, 774), (52895, 288), (53325, 1293), (54661, 1337), (54704, 685),
  (57999, 963), (58702, 1895), (58720, 1903), (59286, 1782), (60509, 1146),
  (61084, 1810), (61156, 871), (64606, 1589), (70167, 1199), (73397, 880),
  (76217, 1215), (79665, 441), (81529, 1729), (83131, 1334), (83170, 618),
  (84536, 1055), (86638, 1674), (88911, 1740), (90915, 1471), (91714, 1814),
  (91760, 1189), (94947, 1747), (96656, 245), (96676, 856), (97392, 1767),
  (98111, 701), (100150, 1076), (100253, 1484), (101639, 332), (106373, 1270),
  (108503, 1456), (109762, 955), (112951, 1331), (116001, 1559), (117099, 1851),
  (117145, 1344), (118715, 543), (118787, 1212), (119819, 918), (121008, 614)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X0Y0_check. -/
theorem X0Split75A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X0Y0_pairs. -/
theorem X0Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split75A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X0_pairs. -/
theorem X0Split75A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0_pairs. -/
theorem X0Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split75A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split75_check. -/
theorem X0Split75_check : checkSplit m4TX0 (3, 1, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split75A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X0Y0Certs : List (Nat × Nat) := [
  (513, 1899), (9837, 938), (18878, 476), (27497, 601), (28576, 1164),
  (30208, 1205), (32785, 1151), (50948, 171), (51452, 1117), (52513, 546),
  (53995, 906), (56562, 1170), (64451, 1697), (69306, 832), (74418, 436),
  (82759, 1645), (83989, 1791), (85872, 206), (101642, 1602), (104336, 1433)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X0Y0_check. -/
theorem X0Split76A0X0Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X0Y0_pairs. -/
theorem X0Split76A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X0_pairs. -/
theorem X0Split76A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X1Y0Certs : List (Nat × Nat) := [
  (18674, 769), (24398, 1595), (31602, 954), (32915, 1661), (54237, 1263),
  (64574, 573), (66067, 1036), (67231, 1872), (69907, 1006), (79683, 755),
  (107629, 1135)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X1Y0_check. -/
theorem X0Split76A0X1Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X1Y0_pairs. -/
theorem X0Split76A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X1_pairs. -/
theorem X0Split76A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X2Y0Certs : List (Nat × Nat) := [
  (1893, 1018), (19274, 419), (20247, 200), (24757, 1080), (31893, 1382),
  (41376, 1122), (44941, 477), (55070, 1688), (61498, 661), (69863, 580),
  (74567, 778), (78668, 987), (78937, 138), (87439, 1536), (89711, 878),
  (98372, 1775), (111144, 1850)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X2Y0_check. -/
theorem X0Split76A0X2Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X2Y0_pairs. -/
theorem X0Split76A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk2 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X2_pairs. -/
theorem X0Split76A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X3Y0Certs : List (Nat × Nat) := [
  (2278, 180), (5508, 482), (17459, 1432), (32369, 1287), (43639, 1974),
  (53936, 1181), (66944, 1258), (80690, 1599), (109653, 1326)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X3Y0_check. -/
theorem X0Split76A0X3Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X3Y0_pairs. -/
theorem X0Split76A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk3 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X3_pairs. -/
theorem X0Split76A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X4Y0Certs : List (Nat × Nat) := [
  (3859, 1269), (14466, 1966), (26764, 1271), (27039, 1458), (29338, 144),
  (77854, 1078), (80914, 1728), (94957, 406), (100359, 98), (101834, 1578),
  (104741, 855), (108706, 1518), (111305, 586)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X4Y0_check. -/
theorem X0Split76A0X4Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X4Y0_pairs. -/
theorem X0Split76A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk4 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X4_pairs. -/
theorem X0Split76A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X5Y0Certs : List (Nat × Nat) := [
  (12353, 1303), (22329, 1715), (34986, 734), (36230, 1526), (55585, 1763),
  (77290, 575), (86131, 1548), (90677, 1134)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X5Y0_check. -/
theorem X0Split76A0X5Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X5Y0_pairs. -/
theorem X0Split76A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk5 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X5_pairs. -/
theorem X0Split76A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X6Y0Certs : List (Nat × Nat) := [
  (251, 850), (1207, 467), (20294, 1638), (36384, 176), (39844, 481),
  (56682, 317), (62025, 957), (64700, 1723), (69806, 142), (77359, 527),
  (87120, 1158), (99112, 270), (103974, 1017), (104881, 1970)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X6Y0_check. -/
theorem X0Split76A0X6Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X6Y0_pairs. -/
theorem X0Split76A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk6 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X6_pairs. -/
theorem X0Split76A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X7Y0Certs : List (Nat × Nat) := [
  (1163, 1278), (13479, 1455), (13803, 364), (34825, 1890), (39356, 1254),
  (53219, 1703), (57872, 1909), (71881, 427), (74920, 588), (76333, 439),
  (80196, 970), (97585, 1142), (107346, 405)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X7Y0_check. -/
theorem X0Split76A0X7Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X7Y0_pairs. -/
theorem X0Split76A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X7Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk7 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X7_pairs. -/
theorem X0Split76A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X8Y0Certs : List (Nat × Nat) := [
  (7480, 870), (34230, 1138), (47081, 1789), (54842, 1745), (61319, 373),
  (71127, 1689), (83509, 1407), (88582, 1748), (88900, 1541), (91504, 541),
  (92962, 374), (109778, 941)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X8Y0_check. -/
theorem X0Split76A0X8Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X8Y0_pairs. -/
theorem X0Split76A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X8Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk8 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X8_pairs. -/
theorem X0Split76A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X9Y0Certs : List (Nat × Nat) := [
  (63130, 1633), (68755, 1200), (88549, 833), (89892, 1777), (96528, 277),
  (97994, 1861), (99530, 929), (102896, 953), (107189, 1862)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X9Y0_check. -/
theorem X0Split76A0X9Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X9Y0_pairs. -/
theorem X0Split76A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X9Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk9 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X9_pairs. -/
theorem X0Split76A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X10Y0Certs : List (Nat × Nat) := [
  (34, 316), (26857, 368), (27846, 1073), (41589, 491), (47806, 780),
  (68389, 1990), (86455, 1173), (92648, 590), (93549, 432), (98673, 968)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X10Y0_check. -/
theorem X0Split76A0X10Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X10Y0_pairs. -/
theorem X0Split76A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X10Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk10 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X10_pairs. -/
theorem X0Split76A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X11Y0Certs : List (Nat × Nat) := [
  (11994, 674), (19062, 1464), (22588, 1133), (29135, 1047), (30982, 1659),
  (41993, 877), (50097, 1290), (58333, 1547), (64069, 1737), (78718, 1585),
  (84211, 1756), (105197, 1514), (105648, 759)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X11Y0_check. -/
theorem X0Split76A0X11Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X11Y0_pairs. -/
theorem X0Split76A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X11Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk11 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X11_pairs. -/
theorem X0Split76A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X12Y0Certs : List (Nat × Nat) := [
  (21266, 486), (25752, 1079), (32947, 1709), (52037, 757), (59854, 247),
  (65464, 864), (69805, 353), (72075, 882), (75711, 1474), (86398, 663),
  (89679, 1727), (92265, 1437)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X12Y0_check. -/
theorem X0Split76A0X12Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X12Y0_pairs. -/
theorem X0Split76A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X12Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk12 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X12_pairs. -/
theorem X0Split76A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X13Y0Certs : List (Nat × Nat) := [
  (6062, 937), (23142, 351), (34569, 1483), (46441, 1248), (69383, 603),
  (95838, 1896), (98105, 667)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X13Y0_check. -/
theorem X0Split76A0X13Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X13Y0_pairs. -/
theorem X0Split76A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X13Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk13 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X13_pairs. -/
theorem X0Split76A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X14Y0Certs : List (Nat × Nat) := [
  (6869, 607), (9518, 1423), (12477, 1938), (14255, 1457), (18125, 694),
  (22466, 649), (24463, 672), (32227, 1089), (47145, 1720), (68413, 1908),
  (71703, 545), (73563, 1129), (78975, 1284), (97844, 824), (101519, 1954),
  (108523, 1171), (110413, 1377)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X14Y0_check. -/
theorem X0Split76A0X14Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X14Y0_pairs. -/
theorem X0Split76A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X14Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk14 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X14_pairs. -/
theorem X0Split76A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X15Y0Certs : List (Nat × Nat) := [
  (27828, 1853), (27870, 1313), (44344, 1783), (52137, 1160), (54039, 978),
  (59346, 1636), (80415, 1308), (84035, 576), (89496, 738), (91730, 1320)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X15Y0_check. -/
theorem X0Split76A0X15Y0_check : checkGrid m4TX0 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X15Y0_pairs. -/
theorem X0Split76A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X15Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk15 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X15_pairs. -/
theorem X0Split76A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0_pairs. -/
theorem X0Split76A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split76A0X0_pairs x hx y hy hw
  · exact X0Split76A0X1_pairs x hx y hy hw
  · exact X0Split76A0X2_pairs x hx y hy hw
  · exact X0Split76A0X3_pairs x hx y hy hw
  · exact X0Split76A0X4_pairs x hx y hy hw
  · exact X0Split76A0X5_pairs x hx y hy hw
  · exact X0Split76A0X6_pairs x hx y hy hw
  · exact X0Split76A0X7_pairs x hx y hy hw
  · exact X0Split76A0X8_pairs x hx y hy hw
  · exact X0Split76A0X9_pairs x hx y hy hw
  · exact X0Split76A0X10_pairs x hx y hy hw
  · exact X0Split76A0X11_pairs x hx y hy hw
  · exact X0Split76A0X12_pairs x hx y hy hw
  · exact X0Split76A0X13_pairs x hx y hy hw
  · exact X0Split76A0X14_pairs x hx y hy hw
  · exact X0Split76A0X15_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split76_check. -/
theorem X0Split76_check : checkSplit m4TX0 (3, 2, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X0Y0Certs : List (Nat × Nat) := [
  (6892, 1554), (27823, 1857), (27875, 145), (28553, 1104), (32906, 1115),
  (56779, 866), (61426, 349), (64373, 1918), (64765, 1671), (68702, 1832),
  (78089, 843), (83822, 1236), (87268, 1049), (92112, 1364)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X0Y0_check. -/
theorem X0Split77A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X0Y0_pairs. -/
theorem X0Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X0_pairs. -/
theorem X0Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X1Y0Certs : List (Nat × Nat) := [
  (9479, 1430), (17166, 743), (33014, 1687), (44305, 1584), (47220, 915),
  (64544, 594), (65354, 375), (65703, 100), (79653, 198), (81418, 279),
  (100897, 1844)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X1Y0_check. -/
theorem X0Split77A0X1Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X1Y0_pairs. -/
theorem X0Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X1_pairs. -/
theorem X0Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X2Y0Certs : List (Nat × Nat) := [
  (14837, 196), (16308, 803), (41602, 1103), (55872, 728), (60366, 1383),
  (61421, 320), (68354, 238), (74552, 611), (78278, 1845), (79688, 311),
  (96761, 727), (98660, 1478)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X2Y0_check. -/
theorem X0Split77A0X2Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X2Y0_pairs. -/
theorem X0Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk2 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X2_pairs. -/
theorem X0Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X3Y0Certs : List (Nat × Nat) := [
  (1254, 1667), (2615, 43), (7332, 1604), (15680, 105), (16310, 807),
  (26696, 587), (32621, 1965), (40030, 78), (46007, 1371), (75367, 409),
  (82931, 1116), (97436, 1964), (104544, 525), (106457, 1281)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X3Y0_check. -/
theorem X0Split77A0X3Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X3Y0_pairs. -/
theorem X0Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk3 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X3_pairs. -/
theorem X0Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X4Y0Certs : List (Nat × Nat) := [
  (2752, 520), (29289, 526), (47410, 1952), (54280, 1399), (55865, 677),
  (73531, 94), (81545, 742), (96740, 627), (100186, 504), (101564, 781),
  (101863, 280), (111079, 568)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X4Y0_check. -/
theorem X0Split77A0X4Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X4Y0_pairs. -/
theorem X0Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk4 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X4_pairs. -/
theorem X0Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X5Y0Certs : List (Nat × Nat) := [
  (12307, 465), (15391, 605), (18585, 1267), (28212, 1603), (36993, 99),
  (57356, 1593), (65327, 292), (91909, 459), (97799, 1521), (105396, 463),
  (107467, 114)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X5Y0_check. -/
theorem X0Split77A0X5Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X5Y0_pairs. -/
theorem X0Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk5 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X5_pairs. -/
theorem X0Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X6Y0Certs : List (Nat × Nat) := [
  (4058, 522), (10720, 1111), (15123, 1376), (21538, 836), (56559, 63),
  (72160, 1673), (79041, 1245), (84096, 514), (87185, 678), (97150, 528)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X6Y0_check. -/
theorem X0Split77A0X6Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X6Y0_pairs. -/
theorem X0Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk6 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X6_pairs. -/
theorem X0Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X7Y0Certs : List (Nat × Nat) := [
  (1060, 723), (12269, 335), (16866, 1384), (19623, 199), (20626, 662),
  (49894, 1242), (53453, 1664), (59094, 1576), (73154, 283), (76587, 126),
  (82187, 1831), (95341, 290), (95746, 195), (110910, 1865)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X7Y0_check. -/
theorem X0Split77A0X7Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X7Y0_pairs. -/
theorem X0Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X7Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk7 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X7_pairs. -/
theorem X0Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X8Y0Certs : List (Nat × Nat) := [
  (8991, 1153), (17241, 1101), (25619, 1686), (34152, 829), (38547, 1042),
  (41291, 1760), (41818, 235), (54205, 1034), (60974, 284), (92922, 1044),
  (104645, 943)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X8Y0_check. -/
theorem X0Split77A0X8Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X8Y0_pairs. -/
theorem X0Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X8Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk8 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X8_pairs. -/
theorem X0Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X9Y0Certs : List (Nat × Nat) := [
  (5463, 928), (16745, 806), (20741, 1177), (32707, 309), (40242, 831),
  (53946, 59), (56620, 269), (69481, 1277), (89854, 934), (91603, 1002),
  (96390, 1003), (97764, 1339), (98041, 604)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X9Y0_check. -/
theorem X0Split77A0X9Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X9Y0_pairs. -/
theorem X0Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X9Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk9 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X9_pairs. -/
theorem X0Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X10Y0Certs : List (Nat × Nat) := [
  (6, 57), (11046, 640), (14754, 1743), (29411, 1040), (46015, 1397),
  (47786, 1594), (50499, 165), (57071, 319), (59691, 356), (63778, 1048),
  (70642, 641), (86248, 428), (103641, 403)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X10Y0_check. -/
theorem X0Split77A0X10Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X10Y0_pairs. -/
theorem X0Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X10Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk10 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X10_pairs. -/
theorem X0Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X11Y0Certs : List (Nat × Nat) := [
  (2529, 1511), (11788, 174), (26363, 1022), (31710, 1691), (40125, 390),
  (42056, 1176), (56956, 1829), (62735, 352), (84257, 1234), (86518, 1682),
  (103718, 705), (108225, 1438), (110631, 516)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X11Y0_check. -/
theorem X0Split77A0X11Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X11Y0_pairs. -/
theorem X0Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X11Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk11 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X11_pairs. -/
theorem X0Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X12Y0Certs : List (Nat × Nat) := [
  (3607, 466), (5512, 1159), (32557, 1553), (46062, 1681), (51818, 208),
  (56282, 612), (72300, 337), (77054, 236), (84124, 620), (84514, 460),
  (89121, 1662), (89954, 1429), (105188, 1510)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X12Y0_check. -/
theorem X0Split77A0X12Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X12Y0_pairs. -/
theorem X0Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X12Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk12 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X12_pairs. -/
theorem X0Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X13Y0Certs : List (Nat × Nat) := [
  (8173, 1422), (19352, 801), (24638, 1105), (28321, 194), (29980, 1755),
  (35103, 1239), (46413, 1238), (53685, 656), (64534, 570), (69522, 1515),
  (83993, 162), (86727, 589), (88769, 137), (98046, 638)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X13Y0_check. -/
theorem X0Split77A0X13Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X13Y0_pairs. -/
theorem X0Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X13Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk13 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X13_pairs. -/
theorem X0Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X14Y0Certs : List (Nat × Nat) := [
  (24398, 161), (32815, 725), (37219, 935), (59394, 900), (65307, 232),
  (75889, 737), (90473, 1917), (108426, 404), (110439, 1668)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X14Y0_check. -/
theorem X0Split77A0X14Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X14Y0_pairs. -/
theorem X0Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X14Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk14 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X14_pairs. -/
theorem X0Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X15Y0Certs : List (Nat × Nat) := [
  (998, 469), (12846, 898), (21990, 913), (26399, 1216), (32495, 1243),
  (35933, 1021), (44186, 974), (61013, 414), (80174, 484), (84970, 529),
  (91974, 707)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X15Y0_check. -/
theorem X0Split77A0X15Y0_check : checkGrid m4TX0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X15Y0_pairs. -/
theorem X0Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X15Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk15 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X15_pairs. -/
theorem X0Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0_pairs. -/
theorem X0Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split77A0X0_pairs x hx y hy hw
  · exact X0Split77A0X1_pairs x hx y hy hw
  · exact X0Split77A0X2_pairs x hx y hy hw
  · exact X0Split77A0X3_pairs x hx y hy hw
  · exact X0Split77A0X4_pairs x hx y hy hw
  · exact X0Split77A0X5_pairs x hx y hy hw
  · exact X0Split77A0X6_pairs x hx y hy hw
  · exact X0Split77A0X7_pairs x hx y hy hw
  · exact X0Split77A0X8_pairs x hx y hy hw
  · exact X0Split77A0X9_pairs x hx y hy hw
  · exact X0Split77A0X10_pairs x hx y hy hw
  · exact X0Split77A0X11_pairs x hx y hy hw
  · exact X0Split77A0X12_pairs x hx y hy hw
  · exact X0Split77A0X13_pairs x hx y hy hw
  · exact X0Split77A0X14_pairs x hx y hy hw
  · exact X0Split77A0X15_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split77_check. -/
theorem X0Split77_check : checkSplit m4TX0 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split78A0X0Y0Certs : List (Nat × Nat) := [
  (5336, 1355), (5639, 1827), (11271, 789), (12010, 191), (12014, 344),
  (12041, 219), (14311, 9), (16494, 1096), (16952, 25), (16967, 499),
  (17161, 16), (21935, 74), (22871, 225), (25445, 71), (25448, 130),
  (30189, 155), (30902, 27), (33828, 561), (33839, 1817), (35671, 12),
  (36344, 346), (37426, 447), (37430, 722), (37487, 494), (40889, 1823),
  (41091, 788), (42364, 50), (45813, 37), (47016, 91), (47033, 998),
  (47128, 1657), (47734, 51), (49085, 66), (50955, 389), (54184, 55),
  (54187, 109), (54995, 68), (55463, 997), (57100, 182), (57822, 259),
  (58547, 495), (62059, 636), (62070, 1), (62081, 216), (64005, 388),
  (65166, 87), (71377, 108), (72766, 449), (72874, 52), (73910, 720),
  (75502, 888), (75505, 1231), (75593, 994), (77631, 787), (77634, 1100),
  (79371, 796), (80712, 260), (80727, 1501), (80918, 132), (81866, 1354),
  (81969, 156), (84010, 185), (84555, 378), (88398, 559), (89471, 214),
  (90879, 149), (90883, 300), (92230, 187), (92877, 1503), (95236, 443),
  (96382, 896), (96503, 995), (100316, 1350), (100318, 1658), (101487, 1499),
  (101905, 1230), (102451, 13), (102453, 32), (103543, 299), (105532, 893),
  (105669, 157), (112020, 4), (113816, 1349), (113897, 496), (115905, 379),
  (115909, 637), (116037, 1500), (117239, 1826), (117796, 451), (119392, 887)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X0Y0_check. -/
theorem X0Split78A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X0Y0_pairs. -/
theorem X0Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split78A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X0_pairs. -/
theorem X0Split78A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0_pairs. -/
theorem X0Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split78A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split78_check. -/
theorem X0Split78_check : checkSplit m4TX0 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X0Y0_check. -/
theorem X0Split79A0X0Y0_check : checkGrid m4TX0 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X0Y0_pairs. -/
theorem X0Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split79A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X0_pairs. -/
theorem X0Split79A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0_pairs. -/
theorem X0Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split79A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split79_check. -/
theorem X0Split79_check : checkSplit m4TX0 (3, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split79A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X0Y0Certs : List (Nat × Nat) := [
  (240, 872), (757, 1989), (2087, 1156), (2334, 1470), (2562, 1473),
  (2724, 1485), (4202, 775), (4908, 1943), (5259, 865), (6024, 1988),
  (6790, 1808), (8257, 838), (8790, 1519), (9607, 333), (9967, 1758),
  (10441, 1953), (11709, 1336), (12064, 1813), (13054, 1579), (13920, 103),
  (14093, 1039), (15347, 847), (15470, 1333), (15778, 1157), (16556, 660),
  (16780, 1295), (16827, 1863), (18271, 1746), (18894, 700), (19011, 1393),
  (19486, 699), (19840, 1441), (20274, 440), (21729, 1883), (21897, 1583),
  (23022, 287), (23314, 617), (23908, 1211), (23917, 1454), (25332, 883),
  (25428, 750), (25637, 911), (25837, 1759), (26829, 1210), (26850, 1280)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X0Y0_check. -/
theorem X0Split80A0X0Y0_check : checkGrid m4TX0 1 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X0Y0_pairs. -/
theorem X0Split80A0X0Y0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S32768Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X0_pairs. -/
theorem X0Split80A0X0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0_pairs. -/
theorem X0Split80A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split80A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split80_check. -/
theorem X0Split80_check : checkSplit m4TX0 (4, 0, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split80A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X0Y0Certs : List (Nat × Nat) := [
  (43612, 1955), (47431, 920)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X0Y0_check. -/
theorem X0Split81A0X0Y0_check : checkGrid m4TX0 1 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X0Y0_pairs. -/
theorem X0Split81A0X0Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S4096Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X0_pairs. -/
theorem X0Split81A0X0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X1Y0Certs : List (Nat × Nat) := [
  (7270, 1041), (66365, 523), (71096, 596), (75356, 1463), (81034, 1408),
  (114387, 1749), (119345, 1570)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X1Y0_check. -/
theorem X0Split81A0X1Y0_check : checkGrid m4TX0 1 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X1Y0_pairs. -/
theorem X0Split81A0X1Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S4096Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S4096Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S4096Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X1_pairs. -/
theorem X0Split81A0X1_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X2Y0Certs : List (Nat × Nat) := [
  (17937, 1607), (70719, 917), (114136, 1586)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X2Y0_check. -/
theorem X0Split81A0X2Y0_check : checkGrid m4TX0 1 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X2Y0_pairs. -/
theorem X0Split81A0X2Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S4096Chunk2_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S4096Chunk2 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk2_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S4096Chunk2_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X2_pairs. -/
theorem X0Split81A0X2_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X3Y0Certs : List (Nat × Nat) := [
  (58577, 739), (117821, 354)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X3Y0_check. -/
theorem X0Split81A0X3Y0_check : checkGrid m4TX0 1 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X3Y0_pairs. -/
theorem X0Split81A0X3Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S4096Chunk3_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S4096Chunk3 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk3_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S4096Chunk3_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X3_pairs. -/
theorem X0Split81A0X3_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X4Y0Certs : List (Nat × Nat) := [
  (6239, 1123), (12899, 1848), (15370, 1942), (57694, 487), (69611, 425),
  (89775, 1486), (96946, 1563), (113175, 1402)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X4Y0_check. -/
theorem X0Split81A0X4Y0_check : checkGrid m4TX0 1 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X4Y0_pairs. -/
theorem X0Split81A0X4Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S4096Chunk4_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S4096Chunk4 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk4_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S4096Chunk4_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X4_pairs. -/
theorem X0Split81A0X4_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X5Y0Certs : List (Nat × Nat) := [
  (20153, 1051), (81773, 1272), (101031, 849), (113242, 1929)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X5Y0_check. -/
theorem X0Split81A0X5Y0_check : checkGrid m4TX0 1 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X5Y0_pairs. -/
theorem X0Split81A0X5Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S4096Chunk5_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S4096Chunk5 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk5_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S4096Chunk5_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X5_pairs. -/
theorem X0Split81A0X5_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X6Y0Certs : List (Nat × Nat) := [
  (30211, 210), (33489, 979), (45887, 861), (67161, 1666)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X6Y0_check. -/
theorem X0Split81A0X6Y0_check : checkGrid m4TX0 1 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X6Y0_pairs. -/
theorem X0Split81A0X6Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 1 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S4096Chunk6_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S4096Chunk6 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk6_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks4S4096Chunk6_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X6_pairs. -/
theorem X0Split81A0X6_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0_pairs. -/
theorem X0Split81A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split81A0X0_pairs x hx y hy hw
  · exact X0Split81A0X1_pairs x hx y hy hw
  · exact X0Split81A0X2_pairs x hx y hy hw
  · exact X0Split81A0X3_pairs x hx y hy hw
  · exact X0Split81A0X4_pairs x hx y hy hw
  · exact X0Split81A0X5_pairs x hx y hy hw
  · exact X0Split81A0X6_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split81_check. -/
theorem X0Split81_check : checkSplit m4TX0 (4, 1, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split81A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A0X0Y0Certs : List (Nat × Nat) := [
  (813, 0), (1174, 1241), (2416, 0), (2729, 435), (5554, 1378),
  (8652, 1680), (11386, 289), (14141, 827), (14311, 1696), (15714, 0),
  (16040, 0), (16531, 28), (16760, 876), (19783, 777), (19901, 1361),
  (21113, 899), (21115, 0), (23629, 0), (27347, 1643), (27392, 1875),
  (28743, 0), (31670, 0), (32738, 413), (36119, 0), (38064, 0),
  (38449, 619), (40294, 1082), (42157, 0), (43637, 506), (43679, 655),
  (44558, 704), (48302, 95), (48586, 1233), (49567, 0), (52378, 0),
  (52697, 0), (53084, 82), (53370, 1232), (54847, 0), (55269, 117),
  (57434, 83), (57640, 825), (60747, 1118), (60876, 1841), (62028, 0),
  (62056, 0), (62998, 1517), (63026, 1677), (63519, 0), (64147, 0),
  (66750, 0), (67034, 178), (67155, 598), (68679, 0), (68833, 372),
  (68982, 985), (70119, 0), (73214, 0), (73304, 842), (76602, 0),
  (81240, 0), (81576, 897), (82266, 0), (82644, 0), (84611, 828),
  (84742, 1507), (85523, 0), (89352, 0), (89432, 1007), (89465, 1150),
  (90344, 1217), (90651, 0), (90772, 0), (95190, 1524), (95825, 0),
  (96642, 273), (96952, 1663), (98509, 0), (101832, 0), (103149, 212),
  (103286, 0), (103475, 1660), (106211, 272), (106225, 313), (108165, 0),
  (108436, 456), (109447, 0), (109462, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X0Y0_check. -/
theorem X0Split82A0X0Y0_check : checkGrid m4TX0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X0Y0_pairs. -/
theorem X0Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X0_pairs. -/
theorem X0Split82A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A0X1Y0Certs : List (Nat × Nat) := [
  (1805, 251), (1809, 268), (4884, 361), (5454, 0), (6586, 0),
  (6712, 0), (7025, 252), (7302, 1418), (10995, 454), (11085, 0),
  (11170, 1167), (13658, 643), (13862, 1644), (16844, 0), (23192, 507),
  (23465, 1839), (25688, 0), (26038, 0), (27550, 0), (29499, 1512),
  (30150, 489), (31620, 0), (32305, 0), (33177, 0), (34148, 0),
  (35269, 143), (35370, 490), (35460, 0), (36975, 0), (36994, 0),
  (37090, 0), (38464, 669), (38512, 0), (46498, 0), (46734, 0),
  (46953, 0), (47132, 552), (47140, 585), (47583, 0), (47911, 0),
  (48835, 0), (50207, 666), (50229, 753), (50351, 0), (52023, 1010),
  (53812, 1247), (53926, 1871), (54987, 0), (56617, 0), (57283, 0),
  (57499, 0), (58111, 1005), (58258, 1773), (59659, 250), (59852, 1008),
  (62699, 0), (64665, 0), (66033, 0), (66401, 0), (66452, 0),
  (66830, 1087), (67468, 0), (67736, 0), (68288, 0), (68819, 336),
  (70156, 0), (73149, 0), (73834, 0), (74057, 0), (75445, 0),
  (76445, 1301), (77759, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X1Y0_check. -/
theorem X0Split82A0X1Y0_check : checkGrid m4TX0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X1Y0_pairs. -/
theorem X0Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X1_pairs. -/
theorem X0Split82A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0_pairs. -/
theorem X0Split82A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split82A0X0_pairs x hx y hy hw
  · exact X0Split82A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A1X0Y0Certs : List (Nat × Nat) := [
  (2763, 565), (22295, 400), (22511, 1362), (38003, 0), (40441, 1870),
  (52237, 0), (55576, 1370), (56884, 0), (67911, 0), (69332, 0),
  (91541, 726), (94981, 549), (108369, 213)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X0Y0_check. -/
theorem X0Split82A1X0Y0_check : checkGrid m4TX0 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X0Y0_pairs. -/
theorem X0Split82A1X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X0_pairs. -/
theorem X0Split82A1X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A1X1Y0Certs : List (Nat × Nat) := [
  (18597, 1363), (33389, 0), (38381, 0), (38443, 592), (46633, 0),
  (48471, 0), (56564, 0), (56770, 0), (67597, 0), (73508, 0),
  (73593, 302), (73790, 1088), (77732, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X1Y0_check. -/
theorem X0Split82A1X1Y0_check : checkGrid m4TX0 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X1Y0_pairs. -/
theorem X0Split82A1X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X1_pairs. -/
theorem X0Split82A1X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1_pairs. -/
theorem X0Split82A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split82A1X0_pairs x hx y hy hw
  · exact X0Split82A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A2X0Y0Certs : List (Nat × Nat) := [
  (1176, 0), (5472, 984), (5857, 0), (6843, 0), (21159, 1107),
  (29049, 0), (29896, 0), (52650, 0), (56538, 0), (61745, 0),
  (65057, 924), (65226, 1842), (75025, 0), (81098, 0), (90724, 0),
  (92354, 0), (94720, 0), (97022, 0), (99879, 0), (108610, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X0Y0_check. -/
theorem X0Split82A2X0Y0_check : checkGrid m4TX0 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X0Y0_pairs. -/
theorem X0Split82A2X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X0_pairs. -/
theorem X0Split82A2X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A2X1Y0Certs : List (Nat × Nat) := [
  (5204, 1860), (26240, 0), (28468, 729), (28635, 1525), (29397, 0),
  (31340, 104), (37762, 0), (38310, 0), (51917, 553), (57133, 0),
  (65228, 1846), (66916, 1528), (76418, 1163)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X1Y0_check. -/
theorem X0Split82A2X1Y0_check : checkGrid m4TX0 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X1Y0_pairs. -/
theorem X0Split82A2X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X1_pairs. -/
theorem X0Split82A2X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2_pairs. -/
theorem X0Split82A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split82A2X0_pairs x hx y hy hw
  · exact X0Split82A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A3X0Y0Certs : List (Nat × Nat) := [
  (34118, 0), (58441, 0), (80901, 0), (98083, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X0Y0_check. -/
theorem X0Split82A3X0Y0_check : checkGrid m4TX0 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X0Y0_pairs. -/
theorem X0Split82A3X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X0_pairs. -/
theorem X0Split82A3X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A3X1Y0Certs : List (Nat × Nat) := [
  (30250, 903), (47647, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X1Y0_check. -/
theorem X0Split82A3X1Y0_check : checkGrid m4TX0 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X1Y0_pairs. -/
theorem X0Split82A3X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split82A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X1_pairs. -/
theorem X0Split82A3X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split82A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3_pairs. -/
theorem X0Split82A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split82A3X0_pairs x hx y hy hw
  · exact X0Split82A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split82_check. -/
theorem X0Split82_check : checkSplit m4TX0 (4, 2, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split82A0_pairs x hx y hy hw
    · exact X0Split82A1_pairs x hx y hy hw
    · exact X0Split82A2_pairs x hx y hy hw
    · exact X0Split82A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X0Y0Certs : List (Nat × Nat) := [
  (33208, 1653), (42489, 150), (65688, 562), (66022, 889), (87130, 188),
  (93775, 1225), (101356, 442)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X0Y0_check. -/
theorem X0Split83A0X0Y0_check : checkGrid m4TX0 0 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X0Y0_pairs. -/
theorem X0Split83A0X0Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S4096Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X0_pairs. -/
theorem X0Split83A0X0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X1Y0Certs : List (Nat × Nat) := [
  (5422, 886), (19011, 786), (20777, 493), (28725, 380), (36537, 1493),
  (38528, 133), (59344, 49), (61186, 444), (67365, 384), (102555, 382),
  (109996, 450), (122807, 502)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X1Y0_check. -/
theorem X0Split83A0X1Y0_check : checkGrid m4TX0 0 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X1Y0_pairs. -/
theorem X0Split83A0X1Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S4096Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S4096Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S4096Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X1_pairs. -/
theorem X0Split83A0X1_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X2Y0Certs : List (Nat × Nat) := [
  (3737, 501), (8700, 5), (10016, 1356), (22284, 1094), (27555, 385),
  (28857, 1494), (58831, 8), (64606, 452), (77472, 256), (79235, 69),
  (86851, 11), (108593, 992), (110456, 1352)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X2Y0_check. -/
theorem X0Split83A0X2Y0_check : checkGrid m4TX0 0 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X2Y0_pairs. -/
theorem X0Split83A0X2Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S4096Chunk2_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S4096Chunk2 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk2_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S4096Chunk2_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X2_pairs. -/
theorem X0Split83A0X2_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X3Y0Certs : List (Nat × Nat) := [
  (27837, 1498), (34821, 790), (51305, 70), (52349, 1820), (56084, 345),
  (73294, 47), (75356, 1353), (76513, 294), (90671, 221), (97720, 190),
  (100913, 989), (103371, 792), (119512, 895)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X3Y0_check. -/
theorem X0Split83A0X3Y0_check : checkGrid m4TX0 0 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X3Y0_pairs. -/
theorem X0Split83A0X3Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S4096Chunk3_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S4096Chunk3 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk3_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S4096Chunk3_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X3_pairs. -/
theorem X0Split83A0X3_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X4Y0Certs : List (Nat × Nat) := [
  (20723, 1000), (28682, 26), (30845, 76), (43582, 890), (48423, 34),
  (62601, 794), (63791, 222), (65609, 1822), (70913, 991), (96574, 48),
  (105334, 46)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X4Y0_check. -/
theorem X0Split83A0X4Y0_check : checkGrid m4TX0 0 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X4Y0_pairs. -/
theorem X0Split83A0X4Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S4096Chunk4_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S4096Chunk4 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk4_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S4096Chunk4_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X4_pairs. -/
theorem X0Split83A0X4_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X5Y0Certs : List (Nat × Nat) := [
  (7120, 181), (13810, 189), (19031, 218), (20359, 630), (20799, 152),
  (33666, 86), (46889, 1825), (47495, 73), (55319, 1821), (59851, 14),
  (62600, 716), (109329, 147)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X5Y0_check. -/
theorem X0Split83A0X5Y0_check : checkGrid m4TX0 0 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X5Y0_pairs. -/
theorem X0Split83A0X5Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S4096Chunk5_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S4096Chunk5 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk5_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S4096Chunk5_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X5_pairs. -/
theorem X0Split83A0X5_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X6Y0Certs : List (Nat × Nat) := [
  (4586, 1357), (14581, 18), (14947, 112), (31127, 503), (39941, 223),
  (48537, 1496), (77199, 151)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X6Y0_check. -/
theorem X0Split83A0X6Y0_check : checkGrid m4TX0 0 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X6Y0_pairs. -/
theorem X0Split83A0X6Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S4096Chunk6_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S4096Chunk6 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk6_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S4096Chunk6_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X6_pairs. -/
theorem X0Split83A0X6_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0_pairs. -/
theorem X0Split83A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split83A0X0_pairs x hx y hy hw
  · exact X0Split83A0X1_pairs x hx y hy hw
  · exact X0Split83A0X2_pairs x hx y hy hw
  · exact X0Split83A0X3_pairs x hx y hy hw
  · exact X0Split83A0X4_pairs x hx y hy hw
  · exact X0Split83A0X5_pairs x hx y hy hw
  · exact X0Split83A0X6_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split83_check. -/
theorem X0Split83_check : checkSplit m4TX0 (4, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split83A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X0Y0_check. -/
theorem X0Split84A0X0Y0_check : checkGrid m4TX0 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X0Y0_pairs. -/
theorem X0Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S32768Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X0_pairs. -/
theorem X0Split84A0X0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0_pairs. -/
theorem X0Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split84A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split84_check. -/
theorem X0Split84_check : checkSplit m4TX0 (4, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split84A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A0X0Y0Certs : List (Nat × Nat) := [
  (145, 207), (165, 230), (229, 271), (586, 0), (647, 483),
  (688, 513), (781, 547), (1022, 665), (1304, 779), (1503, 868),
  (1505, 0), (1813, 1020), (1977, 1081), (2040, 1119), (2436, 1282),
  (2771, 0), (2897, 1477), (2907, 1480), (2959, 1523), (3045, 0),
  (3220, 0), (3359, 1698), (3531, 1761), (3648, 0), (3757, 1869),
  (3882, 1916), (4058, 1994)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0Y0_check. -/
theorem X0Split85A0X0Y0_check : checkGrid m4TX0 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0Y0_pairs. -/
theorem X0Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X0Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0_pairs. -/
theorem X0Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split85A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0_pairs. -/
theorem X0Split85A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split85A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A1X0Y0Certs : List (Nat × Nat) := [
  (14, 81), (533, 430), (859, 591), (1721, 0), (3042, 1552)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0Y0_check. -/
theorem X0Split85A1X0Y0_check : checkGrid m4TX0 2 91076351 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0Y0_pairs. -/
theorem X0Split85A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X0Split85A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0_pairs. -/
theorem X0Split85A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split85A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1_pairs. -/
theorem X0Split85A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split85A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A2X0Y0Certs : List (Nat × Nat) := [
  (198, 248), (1733, 976), (2039, 0), (2158, 1162), (3247, 1642)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0Y0_check. -/
theorem X0Split85A2X0Y0_check : checkGrid m4TX0 2 985062231 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0Y0_pairs. -/
theorem X0Split85A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X0Split85A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0_pairs. -/
theorem X0Split85A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split85A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2_pairs. -/
theorem X0Split85A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split85A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A3X0Y0Certs : List (Nat × Nat) := [
  (1726, 973), (2109, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0Y0_check. -/
theorem X0Split85A3X0Y0_check : checkGrid m4TX0 2 1071345064 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0Y0_pairs. -/
theorem X0Split85A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X0Split85A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0_pairs. -/
theorem X0Split85A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split85A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3_pairs. -/
theorem X0Split85A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split85A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split85_check. -/
theorem X0Split85_check : checkSplit m4TX0 (5, 0, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split85A0_pairs x hx y hy hw
    · exact X0Split85A1_pairs x hx y hy hw
    · exact X0Split85A2_pairs x hx y hy hw
    · exact X0Split85A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split86A0X0Y0Certs : List (Nat × Nat) := [
  (752, 0), (1147, 0), (1668, 0), (2009, 1058), (2084, 1428),
  (3456, 0), (4288, 1619), (4834, 201), (4896, 402), (6102, 0),
  (6573, 197), (6836, 0), (6957, 1975), (7015, 0), (7116, 0),
  (7349, 1685), (7818, 0), (8507, 0), (8740, 0), (8768, 0),
  (9062, 0), (9195, 239), (9714, 524), (9814, 0), (9997, 1912),
  (10246, 0), (10581, 0), (11100, 0), (11366, 229), (11577, 1043),
  (11751, 58), (11817, 0), (12059, 0), (12091, 1446), (12323, 0),
  (12489, 0), (12555, 0), (12626, 79), (12681, 0), (12979, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A0X0Y0_check. -/
theorem X0Split86A0X0Y0_check : checkGrid m4TX0 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A0X0Y0_pairs. -/
theorem X0Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A0X0_pairs. -/
theorem X0Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A0_pairs. -/
theorem X0Split86A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split86A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split86A1X0Y0Certs : List (Nat × Nat) := [
  (581, 531), (679, 933), (3050, 0), (4612, 1019), (4781, 1963),
  (6141, 0), (7326, 1550), (10159, 569), (11304, 0), (12653, 163),
  (12879, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A1X0Y0_check. -/
theorem X0Split86A1X0Y0_check : checkGrid m4TX0 2 91076351 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A1X0Y0_pairs. -/
theorem X0Split86A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split86A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A1X0_pairs. -/
theorem X0Split86A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A1_pairs. -/
theorem X0Split86A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split86A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split86A2X0Y0Certs : List (Nat × Nat) := [
  (664, 0), (2315, 512), (2546, 1592), (4196, 1114), (4774, 0),
  (5099, 0), (7524, 472), (7617, 830), (7861, 0), (9262, 464),
  (10251, 948), (10306, 0), (10435, 0), (10793, 0), (11870, 0),
  (12416, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A2X0Y0_check. -/
theorem X0Split86A2X0Y0_check : checkGrid m4TX0 2 985062231 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A2X0Y0_pairs. -/
theorem X0Split86A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split86A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A2X0_pairs. -/
theorem X0Split86A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A2_pairs. -/
theorem X0Split86A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split86A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split86A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A3X0Y0_check. -/
theorem X0Split86A3X0Y0_check : checkGrid m4TX0 2 1071345064 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A3X0Y0_pairs. -/
theorem X0Split86A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X0Split86A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A3X0_pairs. -/
theorem X0Split86A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86A3_pairs. -/
theorem X0Split86A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split86A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split86_check. -/
theorem X0Split86_check : checkSplit m4TX0 (5, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split86A0_pairs x hx y hy hw
    · exact X0Split86A1_pairs x hx y hy hw
    · exact X0Split86A2_pairs x hx y hy hw
    · exact X0Split86A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A0X0Y0Certs : List (Nat × Nat) := [
  (1263, 0), (1583, 0), (1719, 0), (2739, 0), (5562, 0),
  (6437, 0), (8134, 0), (9291, 0), (9380, 0), (9582, 0),
  (9857, 0), (10241, 0), (10984, 0), (12173, 0), (12392, 0),
  (12660, 0), (12724, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0X0Y0_check. -/
theorem X0Split87A0X0Y0_check : checkGrid m4TX0 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0X0Y0_pairs. -/
theorem X0Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0X0_pairs. -/
theorem X0Split87A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0_pairs. -/
theorem X0Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A1X0Y0Certs : List (Nat × Nat) := [
  (10466, 0), (11650, 0), (12348, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1X0Y0_check. -/
theorem X0Split87A1X0Y0_check : checkGrid m4TX0 2 91076351 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1X0Y0_pairs. -/
theorem X0Split87A1X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1X0_pairs. -/
theorem X0Split87A1X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1_pairs. -/
theorem X0Split87A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A2X0Y0Certs : List (Nat × Nat) := [
  (1991, 0), (3191, 0), (3431, 0), (4170, 0), (4607, 0),
  (5862, 0), (6254, 0), (6363, 0), (9482, 0), (11090, 0),
  (11415, 0), (11619, 0), (12368, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2X0Y0_check. -/
theorem X0Split87A2X0Y0_check : checkGrid m4TX0 2 985062231 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2X0Y0_pairs. -/
theorem X0Split87A2X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2X0_pairs. -/
theorem X0Split87A2X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2_pairs. -/
theorem X0Split87A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A3X0Y0Certs : List (Nat × Nat) := [
  (4439, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3X0Y0_check. -/
theorem X0Split87A3X0Y0_check : checkGrid m4TX0 2 1071345064 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3X0Y0_pairs. -/
theorem X0Split87A3X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3X0_pairs. -/
theorem X0Split87A3X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3_pairs. -/
theorem X0Split87A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split87_check. -/
theorem X0Split87_check : checkSplit m4TX0 (5, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split87A0_pairs x hx y hy hw
    · exact X0Split87A1_pairs x hx y hy hw
    · exact X0Split87A2_pairs x hx y hy hw
    · exact X0Split87A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A0X0Y0Certs : List (Nat × Nat) := [
  (180, 0), (1982, 0), (2598, 0), (3147, 0), (3739, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X0Y0_check. -/
theorem X0Split88A0X0Y0_check : checkGrid m4TX0 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X0Y0_pairs. -/
theorem X0Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X0_pairs. -/
theorem X0Split88A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0_pairs. -/
theorem X0Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split88A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A1X0Y0Certs : List (Nat × Nat) := [
  (3316, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X0Y0_check. -/
theorem X0Split88A1X0Y0_check : checkGrid m4TX0 2 91076351 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X0Y0_pairs. -/
theorem X0Split88A1X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X0_pairs. -/
theorem X0Split88A1X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1_pairs. -/
theorem X0Split88A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split88A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A2X0Y0Certs : List (Nat × Nat) := [
  (593, 0), (2217, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X0Y0_check. -/
theorem X0Split88A2X0Y0_check : checkGrid m4TX0 2 985062231 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X0Y0_pairs. -/
theorem X0Split88A2X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X0_pairs. -/
theorem X0Split88A2X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2_pairs. -/
theorem X0Split88A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split88A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X0Y0_check. -/
theorem X0Split88A3X0Y0_check : checkGrid m4TX0 2 1071345064 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X0Y0_pairs. -/
theorem X0Split88A3X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X0_pairs. -/
theorem X0Split88A3X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3_pairs. -/
theorem X0Split88A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split88A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split88_check. -/
theorem X0Split88_check : checkSplit m4TX0 (5, 3, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split88A0_pairs x hx y hy hw
    · exact X0Split88A1_pairs x hx y hy hw
    · exact X0Split88A2_pairs x hx y hy hw
    · exact X0Split88A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A0X0Y0_check. -/
theorem X0Split89A0X0Y0_check : checkGrid m4TX0 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A0X0Y0_pairs. -/
theorem X0Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A0X0_pairs. -/
theorem X0Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A0_pairs. -/
theorem X0Split89A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split89A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A1X0Y0_check. -/
theorem X0Split89A1X0Y0_check : checkGrid m4TX0 2 91076351 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A1X0Y0_pairs. -/
theorem X0Split89A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split89A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A1X0_pairs. -/
theorem X0Split89A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A1_pairs. -/
theorem X0Split89A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split89A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A2X0Y0Certs : List (Nat × Nat) := [
  (19, 0), (115, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A2X0Y0_check. -/
theorem X0Split89A2X0Y0_check : checkGrid m4TX0 2 985062231 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A2X0Y0_pairs. -/
theorem X0Split89A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split89A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A2X0_pairs. -/
theorem X0Split89A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A2_pairs. -/
theorem X0Split89A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split89A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A3X0Y0_check. -/
theorem X0Split89A3X0Y0_check : checkGrid m4TX0 2 1071345064 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A3X0Y0_pairs. -/
theorem X0Split89A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X0Split89A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A3X0_pairs. -/
theorem X0Split89A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89A3_pairs. -/
theorem X0Split89A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split89A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split89_check. -/
theorem X0Split89_check : checkSplit m4TX0 (6, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split89A0_pairs x hx y hy hw
    · exact X0Split89A1_pairs x hx y hy hw
    · exact X0Split89A2_pairs x hx y hy hw
    · exact X0Split89A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A0X0Y0Certs : List (Nat × Nat) := [
  (120, 0), (140, 715), (192, 0), (337, 106), (478, 1652),
  (492, 254), (678, 558), (780, 3), (834, 1097)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0X0Y0_check. -/
theorem X0Split90A0X0Y0_check : checkGrid m4TX0 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0X0Y0_pairs. -/
theorem X0Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0X0_pairs. -/
theorem X0Split90A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0_pairs. -/
theorem X0Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A1X0Y0Certs : List (Nat × Nat) := [
  (44, 341), (105, 0), (219, 0), (306, 84), (709, 632),
  (873, 38)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1X0Y0_check. -/
theorem X0Split90A1X0Y0_check : checkGrid m4TX0 2 91076351 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1X0Y0_pairs. -/
theorem X0Split90A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split90A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1X0_pairs. -/
theorem X0Split90A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1_pairs. -/
theorem X0Split90A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A2X0Y0Certs : List (Nat × Nat) := [
  (152, 20), (295, 1224), (321, 0), (523, 296), (638, 131)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2X0Y0_check. -/
theorem X0Split90A2X0Y0_check : checkGrid m4TX0 2 985062231 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2X0Y0_pairs. -/
theorem X0Split90A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split90A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2X0_pairs. -/
theorem X0Split90A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2_pairs. -/
theorem X0Split90A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3X0Y0_check. -/
theorem X0Split90A3X0Y0_check : checkGrid m4TX0 2 1071345064 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3X0Y0_pairs. -/
theorem X0Split90A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X0Split90A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3X0_pairs. -/
theorem X0Split90A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3_pairs. -/
theorem X0Split90A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split90_check. -/
theorem X0Split90_check : checkSplit m4TX0 (6, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split90A0_pairs x hx y hy hw
    · exact X0Split90A1_pairs x hx y hy hw
    · exact X0Split90A2_pairs x hx y hy hw
    · exact X0Split90A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0X0Y0_check. -/
theorem X0Split91A0X0Y0_check : checkGrid m4TX0 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0X0Y0_pairs. -/
theorem X0Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0X0_pairs. -/
theorem X0Split91A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0_pairs. -/
theorem X0Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A1X0Y0Certs : List (Nat × Nat) := [
  (232, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1X0Y0_check. -/
theorem X0Split91A1X0Y0_check : checkGrid m4TX0 2 91076351 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1X0Y0_pairs. -/
theorem X0Split91A1X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1X0_pairs. -/
theorem X0Split91A1X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1_pairs. -/
theorem X0Split91A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A2X0Y0Certs : List (Nat × Nat) := [
  (69, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2X0Y0_check. -/
theorem X0Split91A2X0Y0_check : checkGrid m4TX0 2 985062231 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2X0Y0_pairs. -/
theorem X0Split91A2X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2X0_pairs. -/
theorem X0Split91A2X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2_pairs. -/
theorem X0Split91A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3X0Y0_check. -/
theorem X0Split91A3X0Y0_check : checkGrid m4TX0 2 1071345064 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3X0Y0_pairs. -/
theorem X0Split91A3X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3X0_pairs. -/
theorem X0Split91A3X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3_pairs. -/
theorem X0Split91A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split91_check. -/
theorem X0Split91_check : checkSplit m4TX0 (6, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split91A0_pairs x hx y hy hw
    · exact X0Split91A1_pairs x hx y hy hw
    · exact X0Split91A2_pairs x hx y hy hw
    · exact X0Split91A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0X0Y0_check. -/
theorem X0Split92A0X0Y0_check : checkGrid m4TX0 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0X0Y0_pairs. -/
theorem X0Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0X0_pairs. -/
theorem X0Split92A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0_pairs. -/
theorem X0Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1X0Y0_check. -/
theorem X0Split92A1X0Y0_check : checkGrid m4TX0 2 91076351 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1X0Y0_pairs. -/
theorem X0Split92A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split92A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1X0_pairs. -/
theorem X0Split92A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1_pairs. -/
theorem X0Split92A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2X0Y0_check. -/
theorem X0Split92A2X0Y0_check : checkGrid m4TX0 2 985062231 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2X0Y0_pairs. -/
theorem X0Split92A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split92A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2X0_pairs. -/
theorem X0Split92A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2_pairs. -/
theorem X0Split92A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3X0Y0_check. -/
theorem X0Split92A3X0Y0_check : checkGrid m4TX0 2 1071345064 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3X0Y0_pairs. -/
theorem X0Split92A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X0Split92A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3X0_pairs. -/
theorem X0Split92A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3_pairs. -/
theorem X0Split92A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split92_check. -/
theorem X0Split92_check : checkSplit m4TX0 (7, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split92A0_pairs x hx y hy hw
    · exact X0Split92A1_pairs x hx y hy hw
    · exact X0Split92A2_pairs x hx y hy hw
    · exact X0Split92A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0X0Y0_check. -/
theorem X0Split93A0X0Y0_check : checkGrid m4TX0 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0X0Y0_pairs. -/
theorem X0Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0X0_pairs. -/
theorem X0Split93A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0_pairs. -/
theorem X0Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1X0Y0_check. -/
theorem X0Split93A1X0Y0_check : checkGrid m4TX0 2 91076351 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1X0Y0_pairs. -/
theorem X0Split93A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split93A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1X0_pairs. -/
theorem X0Split93A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1_pairs. -/
theorem X0Split93A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2X0Y0_check. -/
theorem X0Split93A2X0Y0_check : checkGrid m4TX0 2 985062231 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2X0Y0_pairs. -/
theorem X0Split93A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split93A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2X0_pairs. -/
theorem X0Split93A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2_pairs. -/
theorem X0Split93A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3X0Y0_check. -/
theorem X0Split93A3X0Y0_check : checkGrid m4TX0 2 1071345064 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3X0Y0_pairs. -/
theorem X0Split93A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X0Split93A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3X0_pairs. -/
theorem X0Split93A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3_pairs. -/
theorem X0Split93A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split93_check. -/
theorem X0Split93_check : checkSplit m4TX0 (7, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split93A0_pairs x hx y hy hw
    · exact X0Split93A1_pairs x hx y hy hw
    · exact X0Split93A2_pairs x hx y hy hw
    · exact X0Split93A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0X0Y0_check. -/
theorem X0Split94A0X0Y0_check : checkGrid m4TX0 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0X0Y0_pairs. -/
theorem X0Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 8 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0X0_pairs. -/
theorem X0Split94A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 8 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0_pairs. -/
theorem X0Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 8 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1X0Y0_check. -/
theorem X0Split94A1X0Y0_check : checkGrid m4TX0 2 91076351 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1X0Y0_pairs. -/
theorem X0Split94A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 8 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 2 91076351 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split94A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1X0_pairs. -/
theorem X0Split94A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 8 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1_pairs. -/
theorem X0Split94A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 8 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2X0Y0_check. -/
theorem X0Split94A2X0Y0_check : checkGrid m4TX0 2 985062231 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2X0Y0_pairs. -/
theorem X0Split94A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 8 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 2 985062231 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split94A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2X0_pairs. -/
theorem X0Split94A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 8 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2_pairs. -/
theorem X0Split94A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 8 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3X0Y0_check. -/
theorem X0Split94A3X0Y0_check : checkGrid m4TX0 2 1071345064 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3X0Y0_pairs. -/
theorem X0Split94A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 8 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 2 1071345064 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X0Split94A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3X0_pairs. -/
theorem X0Split94A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 8 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3_pairs. -/
theorem X0Split94A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 8 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X0Split94_check. -/
theorem X0Split94_check : checkSplit m4TX0 (8, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split94A0_pairs x hx y hy hw
    · exact X0Split94A1_pairs x hx y hy hw
    · exact X0Split94A2_pairs x hx y hy hw
    · exact X0Split94A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for checkAll_X0. -/
theorem checkAll_X0 : checkAll m4TX0 splitsX0 = true := by
  simp only [checkAll, splitsX0, List.all_cons, List.all_nil,
    X0Split0_check, X0Split1_check, X0Split2_check, X0Split3_check,
    X0Split4_check, X0Split5_check, X0Split6_check, X0Split7_check,
    X0Split8_check, X0Split9_check, X0Split10_check, X0Split11_check,
    X0Split12_check, X0Split13_check, X0Split14_check, X0Split15_check,
    X0Split16_check, X0Split17_check, X0Split18_check, X0Split19_check,
    X0Split20_check, X0Split21_check, X0Split22_check, X0Split23_check,
    X0Split24_check, X0Split25_check, X0Split26_check, X0Split27_check,
    X0Split28_check, X0Split29_check, X0Split30_check, X0Split31_check,
    X0Split32_check, X0Split33_check, X0Split34_check, X0Split35_check,
    X0Split36_check, X0Split37_check, X0Split38_check, X0Split39_check,
    X0Split40_check, X0Split41_check, X0Split42_check, X0Split43_check,
    X0Split44_check, X0Split45_check, X0Split46_check, X0Split47_check,
    X0Split48_check, X0Split49_check, X0Split50_check, X0Split51_check,
    X0Split52_check, X0Split53_check, X0Split54_check, X0Split55_check,
    X0Split56_check, X0Split57_check, X0Split58_check, X0Split59_check,
    X0Split60_check, X0Split61_check, X0Split62_check, X0Split63_check,
    X0Split64_check, X0Split65_check, X0Split66_check, X0Split67_check,
    X0Split68_check, X0Split69_check, X0Split70_check, X0Split71_check,
    X0Split72_check, X0Split73_check, X0Split74_check, X0Split75_check,
    X0Split76_check, X0Split77_check, X0Split78_check, X0Split79_check,
    X0Split80_check, X0Split81_check, X0Split82_check, X0Split83_check,
    X0Split84_check, X0Split85_check, X0Split86_check, X0Split87_check,
    X0Split88_check, X0Split89_check, X0Split90_check, X0Split91_check,
    X0Split92_check, X0Split93_check, X0Split94_check, Bool.and_true]

#print axioms checkAll_X0

end Quantum.Stabilizer.Homological.LP.M150

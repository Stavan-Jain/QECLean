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
def X1Split0A0X0Y0Certs : List (Nat × Nat) := [
  (0, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0X0Y0_check. -/
theorem X1Split0A0X0Y0_check : checkGrid m4TX1 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split0A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0X0Y0_pairs. -/
theorem X1Split0A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 0 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 0
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split0A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split0A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0X0_pairs. -/
theorem X1Split0A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 0 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split0A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0_pairs. -/
theorem X1Split0A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 0 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split0A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split0_check. -/
theorem X1Split0_check : checkSplit m4TX1 (0, 0, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split0A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split1A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0X0Y0_check. -/
theorem X1Split1A0X0Y0_check : checkGrid m4TX1 1 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split1A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0X0Y0_pairs. -/
theorem X1Split1A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split1A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split1A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0X0_pairs. -/
theorem X1Split1A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split1A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0_pairs. -/
theorem X1Split1A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split1A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split1_check. -/
theorem X1Split1_check : checkSplit m4TX1 (0, 0, 2, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split1A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split2A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0X0Y0_check. -/
theorem X1Split2A0X0Y0_check : checkGrid m4TX1 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split2A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0X0Y0_pairs. -/
theorem X1Split2A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 1
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split2A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split2A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0X0_pairs. -/
theorem X1Split2A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split2A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0_pairs. -/
theorem X1Split2A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split2A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split2_check. -/
theorem X1Split2_check : checkSplit m4TX1 (0, 1, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split2A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split3A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0X0Y0_check. -/
theorem X1Split3A0X0Y0_check : checkGrid m4TX1 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split3A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0X0Y0_pairs. -/
theorem X1Split3A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split3A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split3A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0X0_pairs. -/
theorem X1Split3A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split3A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0_pairs. -/
theorem X1Split3A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split3A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split3_check. -/
theorem X1Split3_check : checkSplit m4TX1 (0, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split3A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split4A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0X0Y0_check. -/
theorem X1Split4A0X0Y0_check : checkGrid m4TX1 1 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split4A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0X0Y0_pairs. -/
theorem X1Split4A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 1 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split4A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split4A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0X0_pairs. -/
theorem X1Split4A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 1 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split4A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0_pairs. -/
theorem X1Split4A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 1 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split4A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split4_check. -/
theorem X1Split4_check : checkSplit m4TX1 (1, 0, 1, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split4A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split5A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0X0Y0_check. -/
theorem X1Split5A0X0Y0_check : checkGrid m4TX1 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split5A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0X0Y0_pairs. -/
theorem X1Split5A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 1
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split5A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split5A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0X0_pairs. -/
theorem X1Split5A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split5A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0_pairs. -/
theorem X1Split5A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split5A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split5_check. -/
theorem X1Split5_check : checkSplit m4TX1 (1, 1, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split5A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0X0Y0_check. -/
theorem X1Split6A0X0Y0_check : checkGrid m4TX1 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0X0Y0_pairs. -/
theorem X1Split6A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split6A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0X0_pairs. -/
theorem X1Split6A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0_pairs. -/
theorem X1Split6A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1X0Y0_check. -/
theorem X1Split6A1X0Y0_check : checkGrid m4TX1 2 91076351 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1X0Y0_pairs. -/
theorem X1Split6A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split6A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1X0_pairs. -/
theorem X1Split6A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1_pairs. -/
theorem X1Split6A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2X0Y0_check. -/
theorem X1Split6A2X0Y0_check : checkGrid m4TX1 2 985062231 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2X0Y0_pairs. -/
theorem X1Split6A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split6A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2X0_pairs. -/
theorem X1Split6A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2_pairs. -/
theorem X1Split6A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3X0Y0_check. -/
theorem X1Split6A3X0Y0_check : checkGrid m4TX1 2 1071345064 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3X0Y0_pairs. -/
theorem X1Split6A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 2
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split6A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3X0_pairs. -/
theorem X1Split6A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3_pairs. -/
theorem X1Split6A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split6_check. -/
theorem X1Split6_check : checkSplit m4TX1 (2, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split6A0_pairs x hx y hy hw
    · exact X1Split6A1_pairs x hx y hy hw
    · exact X1Split6A2_pairs x hx y hy hw
    · exact X1Split6A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split7A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0X0Y0_check. -/
theorem X1Split7A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split7A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0X0Y0_pairs. -/
theorem X1Split7A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split7A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split7A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0X0_pairs. -/
theorem X1Split7A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split7A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0_pairs. -/
theorem X1Split7A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split7A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split7_check. -/
theorem X1Split7_check : checkSplit m4TX1 (0, 0, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split7A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split8A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0X0Y0_check. -/
theorem X1Split8A0X0Y0_check : checkGrid m4TX1 1 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split8A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0X0Y0_pairs. -/
theorem X1Split8A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split8A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split8A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0X0_pairs. -/
theorem X1Split8A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split8A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0_pairs. -/
theorem X1Split8A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split8A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split8_check. -/
theorem X1Split8_check : checkSplit m4TX1 (0, 1, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split8A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split9A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split9A0X0Y0_check. -/
theorem X1Split9A0X0Y0_check : checkGrid m4TX1 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split9A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split9A0X0Y0_pairs. -/
theorem X1Split9A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 2
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split9A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split9A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split9A0X0_pairs. -/
theorem X1Split9A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split9A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split9A0_pairs. -/
theorem X1Split9A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split9A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split9_check. -/
theorem X1Split9_check : checkSplit m4TX1 (0, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split9A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split10A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0X0Y0_check. -/
theorem X1Split10A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split10A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0X0Y0_pairs. -/
theorem X1Split10A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split10A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split10A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0X0_pairs. -/
theorem X1Split10A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split10A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0_pairs. -/
theorem X1Split10A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split10A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split10_check. -/
theorem X1Split10_check : checkSplit m4TX1 (0, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split10A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split11A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0X0Y0_check. -/
theorem X1Split11A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split11A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0X0Y0_pairs. -/
theorem X1Split11A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split11A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split11A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0X0_pairs. -/
theorem X1Split11A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split11A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0_pairs. -/
theorem X1Split11A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split11A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split11_check. -/
theorem X1Split11_check : checkSplit m4TX1 (0, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split11A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split12A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0X0Y0_check. -/
theorem X1Split12A0X0Y0_check : checkGrid m4TX1 1 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split12A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0X0Y0_pairs. -/
theorem X1Split12A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split12A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split12A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0X0_pairs. -/
theorem X1Split12A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split12A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0_pairs. -/
theorem X1Split12A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split12A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split12_check. -/
theorem X1Split12_check : checkSplit m4TX1 (1, 0, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split12A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split13A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0X0Y0_check. -/
theorem X1Split13A0X0Y0_check : checkGrid m4TX1 1 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split13A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0X0Y0_pairs. -/
theorem X1Split13A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split13A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split13A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0X0_pairs. -/
theorem X1Split13A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split13A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0_pairs. -/
theorem X1Split13A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split13A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split13_check. -/
theorem X1Split13_check : checkSplit m4TX1 (1, 1, 2, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split13A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split14A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0X0Y0_check. -/
theorem X1Split14A0X0Y0_check : checkGrid m4TX1 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split14A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0X0Y0_pairs. -/
theorem X1Split14A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split14A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split14A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0X0_pairs. -/
theorem X1Split14A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split14A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0_pairs. -/
theorem X1Split14A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split14A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split14_check. -/
theorem X1Split14_check : checkSplit m4TX1 (1, 2, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split14A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split15A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0X0Y0_check. -/
theorem X1Split15A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split15A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0X0Y0_pairs. -/
theorem X1Split15A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split15A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split15A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0X0_pairs. -/
theorem X1Split15A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split15A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0_pairs. -/
theorem X1Split15A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split15A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split15_check. -/
theorem X1Split15_check : checkSplit m4TX1 (1, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split15A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split16A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0X0Y0_check. -/
theorem X1Split16A0X0Y0_check : checkGrid m4TX1 1 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split16A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0X0Y0_pairs. -/
theorem X1Split16A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split16A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split16A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0X0_pairs. -/
theorem X1Split16A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split16A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0_pairs. -/
theorem X1Split16A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split16A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split16_check. -/
theorem X1Split16_check : checkSplit m4TX1 (2, 0, 2, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split16A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0X0Y0_check. -/
theorem X1Split17A0X0Y0_check : checkGrid m4TX1 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0X0Y0_pairs. -/
theorem X1Split17A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split17A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0X0_pairs. -/
theorem X1Split17A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0_pairs. -/
theorem X1Split17A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1X0Y0_check. -/
theorem X1Split17A1X0Y0_check : checkGrid m4TX1 2 91076351 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1X0Y0_pairs. -/
theorem X1Split17A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split17A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1X0_pairs. -/
theorem X1Split17A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1_pairs. -/
theorem X1Split17A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2X0Y0_check. -/
theorem X1Split17A2X0Y0_check : checkGrid m4TX1 2 985062231 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2X0Y0_pairs. -/
theorem X1Split17A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split17A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2X0_pairs. -/
theorem X1Split17A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2_pairs. -/
theorem X1Split17A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3X0Y0_check. -/
theorem X1Split17A3X0Y0_check : checkGrid m4TX1 2 1071345064 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3X0Y0_pairs. -/
theorem X1Split17A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 2
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split17A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3X0_pairs. -/
theorem X1Split17A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3_pairs. -/
theorem X1Split17A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split17_check. -/
theorem X1Split17_check : checkSplit m4TX1 (2, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split17A0_pairs x hx y hy hw
    · exact X1Split17A1_pairs x hx y hy hw
    · exact X1Split17A2_pairs x hx y hy hw
    · exact X1Split17A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split18A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0X0Y0_check. -/
theorem X1Split18A0X0Y0_check : checkGrid m4TX1 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split18A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0X0Y0_pairs. -/
theorem X1Split18A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 2
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split18A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split18A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0X0_pairs. -/
theorem X1Split18A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split18A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0_pairs. -/
theorem X1Split18A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split18A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split18_check. -/
theorem X1Split18_check : checkSplit m4TX1 (2, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split18A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0X0Y0_check. -/
theorem X1Split19A0X0Y0_check : checkGrid m4TX1 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0X0Y0_pairs. -/
theorem X1Split19A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split19A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0X0_pairs. -/
theorem X1Split19A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0_pairs. -/
theorem X1Split19A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1X0Y0_check. -/
theorem X1Split19A1X0Y0_check : checkGrid m4TX1 2 91076351 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1X0Y0_pairs. -/
theorem X1Split19A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split19A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1X0_pairs. -/
theorem X1Split19A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1_pairs. -/
theorem X1Split19A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2X0Y0_check. -/
theorem X1Split19A2X0Y0_check : checkGrid m4TX1 2 985062231 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2X0Y0_pairs. -/
theorem X1Split19A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split19A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2X0_pairs. -/
theorem X1Split19A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2_pairs. -/
theorem X1Split19A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3X0Y0_check. -/
theorem X1Split19A3X0Y0_check : checkGrid m4TX1 2 1071345064 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3X0Y0_pairs. -/
theorem X1Split19A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 3
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split19A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3X0_pairs. -/
theorem X1Split19A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3_pairs. -/
theorem X1Split19A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split19_check. -/
theorem X1Split19_check : checkSplit m4TX1 (3, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split19A0_pairs x hx y hy hw
    · exact X1Split19A1_pairs x hx y hy hw
    · exact X1Split19A2_pairs x hx y hy hw
    · exact X1Split19A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0X0Y0_check. -/
theorem X1Split20A0X0Y0_check : checkGrid m4TX1 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0X0Y0_pairs. -/
theorem X1Split20A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split20A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0X0_pairs. -/
theorem X1Split20A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0_pairs. -/
theorem X1Split20A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1X0Y0_check. -/
theorem X1Split20A1X0Y0_check : checkGrid m4TX1 2 91076351 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1X0Y0_pairs. -/
theorem X1Split20A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split20A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1X0_pairs. -/
theorem X1Split20A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1_pairs. -/
theorem X1Split20A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2X0Y0_check. -/
theorem X1Split20A2X0Y0_check : checkGrid m4TX1 2 985062231 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2X0Y0_pairs. -/
theorem X1Split20A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split20A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2X0_pairs. -/
theorem X1Split20A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2_pairs. -/
theorem X1Split20A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3X0Y0_check. -/
theorem X1Split20A3X0Y0_check : checkGrid m4TX1 2 1071345064 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3X0Y0_pairs. -/
theorem X1Split20A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 3
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split20A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3X0_pairs. -/
theorem X1Split20A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3_pairs. -/
theorem X1Split20A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split20_check. -/
theorem X1Split20_check : checkSplit m4TX1 (3, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split20A0_pairs x hx y hy hw
    · exact X1Split20A1_pairs x hx y hy hw
    · exact X1Split20A2_pairs x hx y hy hw
    · exact X1Split20A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0X0Y0_check. -/
theorem X1Split21A0X0Y0_check : checkGrid m4TX1 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0X0Y0_pairs. -/
theorem X1Split21A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split21A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0X0_pairs. -/
theorem X1Split21A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0_pairs. -/
theorem X1Split21A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1X0Y0_check. -/
theorem X1Split21A1X0Y0_check : checkGrid m4TX1 2 91076351 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1X0Y0_pairs. -/
theorem X1Split21A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split21A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1X0_pairs. -/
theorem X1Split21A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1_pairs. -/
theorem X1Split21A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2X0Y0_check. -/
theorem X1Split21A2X0Y0_check : checkGrid m4TX1 2 985062231 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2X0Y0_pairs. -/
theorem X1Split21A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split21A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2X0_pairs. -/
theorem X1Split21A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2_pairs. -/
theorem X1Split21A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3X0Y0_check. -/
theorem X1Split21A3X0Y0_check : checkGrid m4TX1 2 1071345064 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3X0Y0_pairs. -/
theorem X1Split21A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 4
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split21A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3X0_pairs. -/
theorem X1Split21A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3_pairs. -/
theorem X1Split21A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split21_check. -/
theorem X1Split21_check : checkSplit m4TX1 (4, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split21A0_pairs x hx y hy hw
    · exact X1Split21A1_pairs x hx y hy hw
    · exact X1Split21A2_pairs x hx y hy hw
    · exact X1Split21A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split22A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0X0Y0_check. -/
theorem X1Split22A0X0Y0_check : checkGrid m4TX1 1 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split22A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0X0Y0_pairs. -/
theorem X1Split22A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split22A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split22A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0X0_pairs. -/
theorem X1Split22A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split22A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0_pairs. -/
theorem X1Split22A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split22A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split22_check. -/
theorem X1Split22_check : checkSplit m4TX1 (0, 0, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split22A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split23A0X0Y0Certs : List (Nat × Nat) := [
  (0, 3505), (2, 3502), (6, 3486), (11, 1714), (12, 3393),
  (17, 2719), (18, 2798), (23, 3306), (27, 879), (29, 793)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0X0Y0_check. -/
theorem X1Split23A0X0Y0_check : checkGrid m4TX1 1 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split23A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0X0Y0_pairs. -/
theorem X1Split23A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split23A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split23A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0X0_pairs. -/
theorem X1Split23A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split23A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0_pairs. -/
theorem X1Split23A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split23A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split23_check. -/
theorem X1Split23_check : checkSplit m4TX1 (0, 1, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split23A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split24A0X0Y0Certs : List (Nat × Nat) := [
  (1, 800), (15, 1709), (17, 1728), (66, 2628), (68, 2693),
  (72, 2806), (147, 2772), (153, 3218), (155, 3278), (159, 3397),
  (165, 3447), (264, 3373), (270, 3450), (362, 1639), (368, 2647),
  (374, 3234), (417, 1723), (423, 2729), (429, 3317), (433, 951)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split24A0X0Y0_check. -/
theorem X1Split24A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split24A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split24A0X0Y0_pairs. -/
theorem X1Split24A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split24A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split24A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split24A0X0_pairs. -/
theorem X1Split24A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split24A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split24A0_pairs. -/
theorem X1Split24A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split24A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split24_check. -/
theorem X1Split24_check : checkSplit m4TX1 (0, 2, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split24A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split25A0X0Y0Certs : List (Nat × Nat) := [
  (8, 77), (39, 148), (109, 228), (153, 283), (166, 314),
  (277, 404), (311, 448), (397, 518), (542, 611), (661, 711),
  (697, 757), (735, 776), (741, 779), (893, 897), (952, 928),
  (958, 933), (1056, 1033), (1241, 1177), (1516, 1356), (1746, 1541),
  (1772, 1580), (1837, 1628), (1843, 1633), (1909, 1670), (1919, 1685),
  (1935, 1708), (2210, 1914), (2235, 1945), (2237, 1946), (2506, 2156),
  (2922, 2561), (2942, 2602), (2986, 2627), (3061, 2680), (3080, 2703),
  (3090, 2715), (3184, 2774), (3196, 2805), (3598, 3097), (3606, 3112),
  (3609, 3118), (3669, 3189), (3711, 3213), (3726, 3228), (3802, 3277),
  (3807, 3291), (3818, 3302), (3909, 3370), (4005, 3444), (4017, 3459)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0Y0_check. -/
theorem X1Split25A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split25A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0Y0_pairs. -/
theorem X1Split25A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split25A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X1Split25A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0_pairs. -/
theorem X1Split25A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split25A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0_pairs. -/
theorem X1Split25A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split25A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split25_check. -/
theorem X1Split25_check : checkSplit m4TX1 (0, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split25A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split26A0X0Y0Certs : List (Nat × Nat) := [
  (15, 112), (57, 312), (66, 365), (68, 368), (136, 735),
  (142, 754), (155, 847), (159, 860), (164, 872), (255, 1579),
  (264, 1617), (265, 1627), (357, 2600), (362, 2622), (368, 2679),
  (369, 2700), (406, 3171), (418, 3222), (423, 3261), (429, 3366)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split26A0X0Y0_check. -/
theorem X1Split26A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split26A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split26A0X0Y0_pairs. -/
theorem X1Split26A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split26A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split26A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split26A0X0_pairs. -/
theorem X1Split26A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split26A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split26A0_pairs. -/
theorem X1Split26A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split26A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split26_check. -/
theorem X1Split26_check : checkSplit m4TX1 (0, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split26A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split27A0X0Y0Certs : List (Nat × Nat) := [
  (0, 11), (2, 31), (6, 109), (11, 299), (12, 355),
  (17, 733), (18, 835), (23, 1573), (27, 2575), (29, 3168)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0X0Y0_check. -/
theorem X1Split27A0X0Y0_check : checkGrid m4TX1 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split27A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0X0Y0_pairs. -/
theorem X1Split27A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split27A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split27A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0X0_pairs. -/
theorem X1Split27A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split27A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0_pairs. -/
theorem X1Split27A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split27A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split27_check. -/
theorem X1Split27_check : checkSplit m4TX1 (0, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split27A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split28A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0X0Y0_check. -/
theorem X1Split28A0X0Y0_check : checkGrid m4TX1 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split28A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0X0Y0_pairs. -/
theorem X1Split28A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split28A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split28A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0X0_pairs. -/
theorem X1Split28A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split28A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0_pairs. -/
theorem X1Split28A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split28A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split28_check. -/
theorem X1Split28_check : checkSplit m4TX1 (0, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split28A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split29A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0X0Y0_check. -/
theorem X1Split29A0X0Y0_check : checkGrid m4TX1 1 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split29A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0X0Y0_pairs. -/
theorem X1Split29A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split29A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split29A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0X0_pairs. -/
theorem X1Split29A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split29A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0_pairs. -/
theorem X1Split29A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split29A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split29_check. -/
theorem X1Split29_check : checkSplit m4TX1 (1, 0, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split29A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split30A0X0Y0Certs : List (Nat × Nat) := [
  (33, 1924), (127, 2003), (245, 2475), (283, 2515), (430, 2483),
  (469, 450), (616, 2517), (654, 1037), (772, 680), (866, 1487)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0X0Y0_check. -/
theorem X1Split30A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split30A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0X0Y0_pairs. -/
theorem X1Split30A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split30A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split30A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0X0_pairs. -/
theorem X1Split30A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split30A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0_pairs. -/
theorem X1Split30A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split30A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split30_check. -/
theorem X1Split30_check : checkSplit m4TX1 (1, 1, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split30A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split31A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split31A0X0Y0_check. -/
theorem X1Split31A0X0Y0_check : checkGrid m4TX1 1 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split31A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split31A0X0Y0_pairs. -/
theorem X1Split31A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split31A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split31A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split31A0X0_pairs. -/
theorem X1Split31A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split31A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split31A0_pairs. -/
theorem X1Split31A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split31A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split31_check. -/
theorem X1Split31_check : checkSplit m4TX1 (1, 2, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split31A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split32A0X0Y0Certs : List (Nat × Nat) := [
  (635, 1138), (680, 1454), (2056, 2102), (2085, 2422), (3523, 224),
  (3655, 973), (4220, 2050), (4315, 3018), (6208, 605), (6375, 1810),
  (6858, 2297), (6913, 2903), (8808, 569), (8929, 1345), (9231, 502),
  (9263, 661), (11092, 1268), (11152, 1780), (12189, 75), (12259, 427)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split32A0X0Y0_check. -/
theorem X1Split32A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split32A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split32A0X0Y0_pairs. -/
theorem X1Split32A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split32A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split32A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split32A0X0_pairs. -/
theorem X1Split32A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split32A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split32A0_pairs. -/
theorem X1Split32A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split32A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split32_check. -/
theorem X1Split32_check : checkSplit m4TX1 (1, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split32A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split33A0X0Y0Certs : List (Nat × Nat) := [
  (44, 482), (140, 1100), (244, 58), (295, 2030), (429, 199),
  (478, 2860), (615, 561), (638, 165), (771, 1248), (841, 21)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split33A0X0Y0_check. -/
theorem X1Split33A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split33A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split33A0X0Y0_pairs. -/
theorem X1Split33A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split33A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split33A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split33A0X0_pairs. -/
theorem X1Split33A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split33A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split33A0_pairs. -/
theorem X1Split33A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split33A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split33_check. -/
theorem X1Split33_check : checkSplit m4TX1 (1, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split33A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split34A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split34A0X0Y0_check. -/
theorem X1Split34A0X0Y0_check : checkGrid m4TX1 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split34A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split34A0X0Y0_pairs. -/
theorem X1Split34A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split34A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split34A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split34A0X0_pairs. -/
theorem X1Split34A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split34A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split34A0_pairs. -/
theorem X1Split34A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split34A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split34_check. -/
theorem X1Split34_check : checkSplit m4TX1 (1, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split34A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split35A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split35A0X0Y0_check. -/
theorem X1Split35A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split35A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split35A0X0Y0_pairs. -/
theorem X1Split35A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split35A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split35A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split35A0X0_pairs. -/
theorem X1Split35A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split35A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split35A0_pairs. -/
theorem X1Split35A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split35A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split35_check. -/
theorem X1Split35_check : checkSplit m4TX1 (2, 0, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split35A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split36A0X0Y0Certs : List (Nat × Nat) := [
  (1182, 2022), (3378, 2705), (5162, 473), (5877, 2842), (6690, 3198),
  (7187, 821), (8406, 1086), (9329, 3227), (10193, 1757), (11831, 883)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split36A0X0Y0_check. -/
theorem X1Split36A0X0Y0_check : checkGrid m4TX1 1 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split36A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split36A0X0Y0_pairs. -/
theorem X1Split36A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split36A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split36A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split36A0X0_pairs. -/
theorem X1Split36A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split36A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split36A0_pairs. -/
theorem X1Split36A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split36A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split36_check. -/
theorem X1Split36_check : checkSplit m4TX1 (2, 1, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split36A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split37A0X0Y0Certs : List (Nat × Nat) := [
  (13964, 230), (17247, 1798), (40211, 1112), (43619, 615), (48789, 371),
  (74898, 426), (84694, 2047), (85173, 2500), (89405, 1362), (95054, 1304),
  (97165, 865), (104096, 684)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37A0X0Y0_check. -/
theorem X1Split37A0X0Y0_check : checkGrid m4TX1 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split37A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37A0X0Y0_pairs. -/
theorem X1Split37A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split37A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split37A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37A0X0_pairs. -/
theorem X1Split37A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split37A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split37A0X1Y0Certs : List (Nat × Nat) := [
  (10613, 970), (23442, 2897), (23846, 2598), (28576, 2038), (36353, 1504),
  (53887, 2874), (59708, 585), (60446, 3208)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37A0X1Y0_check. -/
theorem X1Split37A0X1Y0_check : checkGrid m4TX1 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split37A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37A0X1Y0_pairs. -/
theorem X1Split37A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split37A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split37A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37A0X1_pairs. -/
theorem X1Split37A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split37A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37A0_pairs. -/
theorem X1Split37A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split37A0X0_pairs x hx y hy hw
  · exact X1Split37A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split37_check. -/
theorem X1Split37_check : checkSplit m4TX1 (2, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split37A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split38A0X0Y0Certs : List (Nat × Nat) := [
  (220, 240), (1194, 1776), (1216, 632), (2977, 132), (3363, 40),
  (3442, 1393), (5173, 420), (5876, 2266), (6133, 419), (6335, 81),
  (6697, 133), (6776, 2256), (7186, 639), (8419, 965), (9305, 79),
  (9619, 964), (10192, 1399), (11583, 45), (11830, 245), (12114, 1775)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split38A0X0Y0_check. -/
theorem X1Split38A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split38A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split38A0X0Y0_pairs. -/
theorem X1Split38A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split38A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split38A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split38A0X0_pairs. -/
theorem X1Split38A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split38A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split38A0_pairs. -/
theorem X1Split38A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split38A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split38_check. -/
theorem X1Split38_check : checkSplit m4TX1 (2, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split38A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split39A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split39A0X0Y0_check. -/
theorem X1Split39A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split39A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split39A0X0Y0_pairs. -/
theorem X1Split39A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split39A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split39A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split39A0X0_pairs. -/
theorem X1Split39A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split39A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split39A0_pairs. -/
theorem X1Split39A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split39A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split39_check. -/
theorem X1Split39_check : checkSplit m4TX1 (2, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split39A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split40A0X0Y0Certs : List (Nat × Nat) := [
  (116, 1067), (182, 2744), (312, 582), (555, 1988), (608, 2225),
  (752, 3425), (963, 330), (1057, 1302), (1232, 1465), (1429, 665),
  (1535, 2362), (1667, 3156), (1907, 796), (1936, 2916), (2074, 1218),
  (2211, 1091), (2258, 1789), (2494, 2435), (2511, 1270), (2624, 214),
  (2776, 2355), (2844, 3357), (3078, 937), (3180, 1719), (3283, 467),
  (3389, 2905), (3585, 2234), (3655, 1649), (3731, 3179), (4011, 2752)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split40A0X0Y0_check. -/
theorem X1Split40A0X0Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split40A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split40A0X0Y0_pairs. -/
theorem X1Split40A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split40A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split40A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split40A0X0_pairs. -/
theorem X1Split40A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split40A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split40A0_pairs. -/
theorem X1Split40A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split40A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split40_check. -/
theorem X1Split40_check : checkSplit m4TX1 (3, 0, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split40A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split41A0X0Y0Certs : List (Nat × Nat) := [
  (21, 0), (12686, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A0X0Y0_check. -/
theorem X1Split41A0X0Y0_check : checkGrid m4TX1 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A0X0Y0_pairs. -/
theorem X1Split41A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split41A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A0X0_pairs. -/
theorem X1Split41A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split41A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A0_pairs. -/
theorem X1Split41A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split41A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split41A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A1X0Y0_check. -/
theorem X1Split41A1X0Y0_check : checkGrid m4TX1 2 91076351 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A1X0Y0_pairs. -/
theorem X1Split41A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split41A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A1X0_pairs. -/
theorem X1Split41A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split41A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A1_pairs. -/
theorem X1Split41A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split41A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split41A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A2X0Y0_check. -/
theorem X1Split41A2X0Y0_check : checkGrid m4TX1 2 985062231 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A2X0Y0_pairs. -/
theorem X1Split41A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split41A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A2X0_pairs. -/
theorem X1Split41A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split41A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A2_pairs. -/
theorem X1Split41A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split41A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split41A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A3X0Y0_check. -/
theorem X1Split41A3X0Y0_check : checkGrid m4TX1 2 1071345064 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A3X0Y0_pairs. -/
theorem X1Split41A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 3
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split41A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split41A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A3X0_pairs. -/
theorem X1Split41A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split41A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41A3_pairs. -/
theorem X1Split41A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split41A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split41_check. -/
theorem X1Split41_check : checkSplit m4TX1 (3, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split41A0_pairs x hx y hy hw
    · exact X1Split41A1_pairs x hx y hy hw
    · exact X1Split41A2_pairs x hx y hy hw
    · exact X1Split41A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split42A0X0Y0Certs : List (Nat × Nat) := [
  (6859, 0), (8213, 0), (11773, 0), (12145, 0), (12550, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A0X0Y0_check. -/
theorem X1Split42A0X0Y0_check : checkGrid m4TX1 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A0X0Y0_pairs. -/
theorem X1Split42A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split42A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A0X0_pairs. -/
theorem X1Split42A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split42A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A0_pairs. -/
theorem X1Split42A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split42A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split42A1X0Y0Certs : List (Nat × Nat) := [
  (13037, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A1X0Y0_check. -/
theorem X1Split42A1X0Y0_check : checkGrid m4TX1 2 91076351 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A1X0Y0_pairs. -/
theorem X1Split42A1X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split42A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A1X0_pairs. -/
theorem X1Split42A1X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split42A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A1_pairs. -/
theorem X1Split42A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split42A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split42A2X0Y0Certs : List (Nat × Nat) := [
  (9741, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A2X0Y0_check. -/
theorem X1Split42A2X0Y0_check : checkGrid m4TX1 2 985062231 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A2X0Y0_pairs. -/
theorem X1Split42A2X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split42A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A2X0_pairs. -/
theorem X1Split42A2X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split42A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A2_pairs. -/
theorem X1Split42A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split42A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split42A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A3X0Y0_check. -/
theorem X1Split42A3X0Y0_check : checkGrid m4TX1 2 1071345064 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A3X0Y0_pairs. -/
theorem X1Split42A3X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 3
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split42A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split42A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A3X0_pairs. -/
theorem X1Split42A3X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split42A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42A3_pairs. -/
theorem X1Split42A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split42A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split42_check. -/
theorem X1Split42_check : checkSplit m4TX1 (3, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split42A0_pairs x hx y hy hw
    · exact X1Split42A1_pairs x hx y hy hw
    · exact X1Split42A2_pairs x hx y hy hw
    · exact X1Split42A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split43A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split43A0X0Y0_check. -/
theorem X1Split43A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split43A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split43A0X0Y0_pairs. -/
theorem X1Split43A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split43A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split43A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split43A0X0_pairs. -/
theorem X1Split43A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split43A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split43A0_pairs. -/
theorem X1Split43A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split43A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split43_check. -/
theorem X1Split43_check : checkSplit m4TX1 (3, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split43A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split44A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A0X0Y0_check. -/
theorem X1Split44A0X0Y0_check : checkGrid m4TX1 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A0X0Y0_pairs. -/
theorem X1Split44A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split44A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A0X0_pairs. -/
theorem X1Split44A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split44A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A0_pairs. -/
theorem X1Split44A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split44A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split44A1X0Y0Certs : List (Nat × Nat) := [
  (239, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A1X0Y0_check. -/
theorem X1Split44A1X0Y0_check : checkGrid m4TX1 2 91076351 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A1X0Y0_pairs. -/
theorem X1Split44A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split44A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A1X0_pairs. -/
theorem X1Split44A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split44A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A1_pairs. -/
theorem X1Split44A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split44A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split44A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A2X0Y0_check. -/
theorem X1Split44A2X0Y0_check : checkGrid m4TX1 2 985062231 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A2X0Y0_pairs. -/
theorem X1Split44A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split44A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A2X0_pairs. -/
theorem X1Split44A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split44A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A2_pairs. -/
theorem X1Split44A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split44A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split44A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A3X0Y0_check. -/
theorem X1Split44A3X0Y0_check : checkGrid m4TX1 2 1071345064 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A3X0Y0_pairs. -/
theorem X1Split44A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 4
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split44A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split44A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A3X0_pairs. -/
theorem X1Split44A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split44A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44A3_pairs. -/
theorem X1Split44A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split44A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split44_check. -/
theorem X1Split44_check : checkSplit m4TX1 (4, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split44A0_pairs x hx y hy hw
    · exact X1Split44A1_pairs x hx y hy hw
    · exact X1Split44A2_pairs x hx y hy hw
    · exact X1Split44A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split45A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A0X0Y0_check. -/
theorem X1Split45A0X0Y0_check : checkGrid m4TX1 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A0X0Y0_pairs. -/
theorem X1Split45A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split45A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A0X0_pairs. -/
theorem X1Split45A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split45A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A0_pairs. -/
theorem X1Split45A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split45A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split45A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A1X0Y0_check. -/
theorem X1Split45A1X0Y0_check : checkGrid m4TX1 2 91076351 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A1X0Y0_pairs. -/
theorem X1Split45A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split45A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A1X0_pairs. -/
theorem X1Split45A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split45A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A1_pairs. -/
theorem X1Split45A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split45A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split45A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A2X0Y0_check. -/
theorem X1Split45A2X0Y0_check : checkGrid m4TX1 2 985062231 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A2X0Y0_pairs. -/
theorem X1Split45A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split45A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A2X0_pairs. -/
theorem X1Split45A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split45A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A2_pairs. -/
theorem X1Split45A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split45A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split45A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A3X0Y0_check. -/
theorem X1Split45A3X0Y0_check : checkGrid m4TX1 2 1071345064 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A3X0Y0_pairs. -/
theorem X1Split45A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 4
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split45A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split45A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A3X0_pairs. -/
theorem X1Split45A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split45A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45A3_pairs. -/
theorem X1Split45A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split45A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split45_check. -/
theorem X1Split45_check : checkSplit m4TX1 (4, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split45A0_pairs x hx y hy hw
    · exact X1Split45A1_pairs x hx y hy hw
    · exact X1Split45A2_pairs x hx y hy hw
    · exact X1Split45A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split46A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A0X0Y0_check. -/
theorem X1Split46A0X0Y0_check : checkGrid m4TX1 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A0X0Y0_pairs. -/
theorem X1Split46A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split46A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A0X0_pairs. -/
theorem X1Split46A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split46A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A0_pairs. -/
theorem X1Split46A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split46A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split46A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A1X0Y0_check. -/
theorem X1Split46A1X0Y0_check : checkGrid m4TX1 2 91076351 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A1X0Y0_pairs. -/
theorem X1Split46A1X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split46A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A1X0_pairs. -/
theorem X1Split46A1X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split46A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A1_pairs. -/
theorem X1Split46A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split46A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split46A2X0Y0Certs : List (Nat × Nat) := [
  (25, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A2X0Y0_check. -/
theorem X1Split46A2X0Y0_check : checkGrid m4TX1 2 985062231 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A2X0Y0_pairs. -/
theorem X1Split46A2X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split46A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A2X0_pairs. -/
theorem X1Split46A2X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split46A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A2_pairs. -/
theorem X1Split46A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split46A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split46A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A3X0Y0_check. -/
theorem X1Split46A3X0Y0_check : checkGrid m4TX1 2 1071345064 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A3X0Y0_pairs. -/
theorem X1Split46A3X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 4
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split46A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split46A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A3X0_pairs. -/
theorem X1Split46A3X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split46A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46A3_pairs. -/
theorem X1Split46A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split46A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split46_check. -/
theorem X1Split46_check : checkSplit m4TX1 (4, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split46A0_pairs x hx y hy hw
    · exact X1Split46A1_pairs x hx y hy hw
    · exact X1Split46A2_pairs x hx y hy hw
    · exact X1Split46A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split47A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A0X0Y0_check. -/
theorem X1Split47A0X0Y0_check : checkGrid m4TX1 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A0X0Y0_pairs. -/
theorem X1Split47A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split47A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A0X0_pairs. -/
theorem X1Split47A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split47A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A0_pairs. -/
theorem X1Split47A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split47A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split47A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A1X0Y0_check. -/
theorem X1Split47A1X0Y0_check : checkGrid m4TX1 2 91076351 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A1X0Y0_pairs. -/
theorem X1Split47A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split47A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A1X0_pairs. -/
theorem X1Split47A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split47A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A1_pairs. -/
theorem X1Split47A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split47A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split47A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A2X0Y0_check. -/
theorem X1Split47A2X0Y0_check : checkGrid m4TX1 2 985062231 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A2X0Y0_pairs. -/
theorem X1Split47A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split47A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A2X0_pairs. -/
theorem X1Split47A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split47A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A2_pairs. -/
theorem X1Split47A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split47A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split47A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A3X0Y0_check. -/
theorem X1Split47A3X0Y0_check : checkGrid m4TX1 2 1071345064 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A3X0Y0_pairs. -/
theorem X1Split47A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 5
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split47A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split47A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A3X0_pairs. -/
theorem X1Split47A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split47A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47A3_pairs. -/
theorem X1Split47A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split47A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split47_check. -/
theorem X1Split47_check : checkSplit m4TX1 (5, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split47A0_pairs x hx y hy hw
    · exact X1Split47A1_pairs x hx y hy hw
    · exact X1Split47A2_pairs x hx y hy hw
    · exact X1Split47A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split48A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0X0Y0_check. -/
theorem X1Split48A0X0Y0_check : checkGrid m4TX1 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0X0Y0_pairs. -/
theorem X1Split48A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split48A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0X0_pairs. -/
theorem X1Split48A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0_pairs. -/
theorem X1Split48A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split48A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1X0Y0_check. -/
theorem X1Split48A1X0Y0_check : checkGrid m4TX1 2 91076351 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1X0Y0_pairs. -/
theorem X1Split48A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split48A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1X0_pairs. -/
theorem X1Split48A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1_pairs. -/
theorem X1Split48A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split48A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2X0Y0_check. -/
theorem X1Split48A2X0Y0_check : checkGrid m4TX1 2 985062231 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2X0Y0_pairs. -/
theorem X1Split48A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split48A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2X0_pairs. -/
theorem X1Split48A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2_pairs. -/
theorem X1Split48A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split48A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3X0Y0_check. -/
theorem X1Split48A3X0Y0_check : checkGrid m4TX1 2 1071345064 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3X0Y0_pairs. -/
theorem X1Split48A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 5
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split48A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3X0_pairs. -/
theorem X1Split48A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3_pairs. -/
theorem X1Split48A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split48_check. -/
theorem X1Split48_check : checkSplit m4TX1 (5, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split48A0_pairs x hx y hy hw
    · exact X1Split48A1_pairs x hx y hy hw
    · exact X1Split48A2_pairs x hx y hy hw
    · exact X1Split48A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0X0Y0_check. -/
theorem X1Split49A0X0Y0_check : checkGrid m4TX1 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0X0Y0_pairs. -/
theorem X1Split49A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split49A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0X0_pairs. -/
theorem X1Split49A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0_pairs. -/
theorem X1Split49A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1X0Y0_check. -/
theorem X1Split49A1X0Y0_check : checkGrid m4TX1 2 91076351 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1X0Y0_pairs. -/
theorem X1Split49A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split49A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1X0_pairs. -/
theorem X1Split49A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1_pairs. -/
theorem X1Split49A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2X0Y0_check. -/
theorem X1Split49A2X0Y0_check : checkGrid m4TX1 2 985062231 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2X0Y0_pairs. -/
theorem X1Split49A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split49A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2X0_pairs. -/
theorem X1Split49A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2_pairs. -/
theorem X1Split49A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3X0Y0_check. -/
theorem X1Split49A3X0Y0_check : checkGrid m4TX1 2 1071345064 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3X0Y0_pairs. -/
theorem X1Split49A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 6
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split49A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3X0_pairs. -/
theorem X1Split49A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3_pairs. -/
theorem X1Split49A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split49_check. -/
theorem X1Split49_check : checkSplit m4TX1 (6, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split49A0_pairs x hx y hy hw
    · exact X1Split49A1_pairs x hx y hy hw
    · exact X1Split49A2_pairs x hx y hy hw
    · exact X1Split49A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split50A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0X0Y0_check. -/
theorem X1Split50A0X0Y0_check : checkGrid m4TX1 1 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split50A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0X0Y0_pairs. -/
theorem X1Split50A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 8 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split50A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split50A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0X0_pairs. -/
theorem X1Split50A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 8 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split50A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0_pairs. -/
theorem X1Split50A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 8 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split50A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split50_check. -/
theorem X1Split50_check : checkSplit m4TX1 (0, 0, 8, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split50A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split51A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0X0Y0_check. -/
theorem X1Split51A0X0Y0_check : checkGrid m4TX1 1 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split51A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0X0Y0_pairs. -/
theorem X1Split51A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split51A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split51A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0X0_pairs. -/
theorem X1Split51A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split51A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0_pairs. -/
theorem X1Split51A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split51A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split51_check. -/
theorem X1Split51_check : checkSplit m4TX1 (0, 1, 7, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split51A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split52A0X0Y0Certs : List (Nat × Nat) := [
  (14, 1490), (35, 2151), (46, 624), (54, 2478), (55, 3487),
  (57, 3480), (94, 1044), (104, 3089), (124, 1379), (135, 2489),
  (136, 3408), (138, 3401), (142, 3282), (164, 2733), (197, 1940),
  (209, 3085), (215, 2901), (240, 2217), (252, 2535), (255, 2808),
  (259, 2698), (265, 1730), (284, 2334), (313, 2255), (324, 3067),
  (326, 1876), (340, 3147), (357, 3467), (363, 3407), (369, 2814),
  (381, 1369), (397, 3141), (406, 3501), (418, 3385), (424, 2789)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split52A0X0Y0_check. -/
theorem X1Split52A0X0Y0_check : checkGrid m4TX1 1 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split52A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split52A0X0Y0_pairs. -/
theorem X1Split52A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split52A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split52A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split52A0X0_pairs. -/
theorem X1Split52A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split52A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split52A0_pairs. -/
theorem X1Split52A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split52A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split52_check. -/
theorem X1Split52_check : checkSplit m4TX1 (0, 2, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split52A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split53A0X0Y0Certs : List (Nat × Nat) := [
  (8, 1370), (21, 3482), (39, 1879), (109, 2153), (117, 1491),
  (129, 1375), (152, 2476), (153, 2340), (166, 1725), (221, 3383),
  (235, 3318), (237, 3310), (281, 2641), (311, 1496), (319, 2154),
  (386, 1926), (390, 3088), (397, 2939), (542, 3091), (556, 2479),
  (564, 718), (603, 2188), (660, 2485), (661, 1077), (681, 2731),
  (695, 2788), (697, 2795), (735, 3268), (737, 3233), (757, 3471),
  (817, 2785), (831, 2730), (833, 2721), (871, 3404), (873, 3406),
  (882, 1675), (884, 1640), (888, 943), (964, 3308), (1056, 2490),
  (1070, 3093), (1079, 2167), (1082, 1987), (1144, 1235), (1222, 2012),
  (1228, 3083), (1241, 1194), (1361, 1039), (1516, 3096), (1536, 2497),
  (1565, 1556), (1658, 3036), (1745, 2523), (1746, 2007), (1788, 3390),
  (1828, 2648), (1839, 3485), (1843, 3500), (1909, 1641), (1913, 944),
  (1918, 3507), (1924, 901), (1941, 3394), (2035, 622), (2210, 2539),
  (2230, 3103), (2235, 2957), (2237, 2409), (2244, 2907), (2248, 2357),
  (2325, 2245), (2480, 2566), (2487, 3014), (2506, 2186), (2532, 2408),
  (2534, 2958), (2631, 2150), (2687, 2450), (2829, 2304), (2921, 1331),
  (2922, 2533), (2926, 948), (2997, 2782), (3067, 3321), (3072, 2809),
  (3084, 3379), (3089, 2694), (3090, 3479), (3178, 2801), (3184, 2732),
  (3189, 3400), (3190, 1688), (3195, 3478), (3287, 1488), (3363, 3064),
  (3567, 2922), (3574, 1933), (3598, 3016), (3605, 1877), (3606, 1982),
  (3608, 1371), (3609, 2175), (3671, 1705), (3709, 3477), (3715, 3499),
  (3720, 2697), (3790, 3398), (3801, 2800), (3807, 3280), (3818, 2714),
  (3819, 3474), (3918, 3395), (3919, 1710), (3924, 3473), (4007, 3508),
  (4016, 1682), (4017, 3403), (4022, 2691), (4023, 2811), (4028, 3274)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0Y0_check. -/
theorem X1Split53A0X0Y0_check : checkGrid m4TX1 1 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split53A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0Y0_pairs. -/
theorem X1Split53A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split53A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X1Split53A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0_pairs. -/
theorem X1Split53A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split53A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0_pairs. -/
theorem X1Split53A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split53A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split53_check. -/
theorem X1Split53_check : checkSplit m4TX1 (0, 3, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split53A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y0Certs : List (Nat × Nat) := [
  (165, 227), (351, 329), (516, 381), (661, 405), (677, 410),
  (723, 436), (1676, 608), (1930, 670), (2217, 708), (2221, 710),
  (2546, 777), (2560, 780), (2562, 781), (2601, 788), (2617, 792),
  (3081, 863), (3240, 878), (3281, 890), (3295, 892), (3297, 893),
  (3335, 898), (3341, 900), (3741, 930), (3757, 935), (3795, 941),
  (3797, 942), (3806, 947), (3812, 949), (3985, 1003), (4998, 1145),
  (5163, 1160), (5179, 1165), (6137, 1289), (7041, 1352), (7062, 1357),
  (7858, 1472), (8556, 1537), (8564, 1540), (8876, 1595), (9021, 1621),
  (9037, 1623), (9090, 1634), (9536, 1671), (9550, 1673), (9552, 1674),
  (9590, 1679), (9596, 1681), (9603, 1686), (9607, 1687), (9612, 1689),
  (9672, 1699), (9688, 1704), (9737, 1712), (9743, 1713), (9818, 1724),
  (11016, 1844), (11168, 1860), (11701, 1915), (11965, 1947), (11978, 1948),
  (12177, 1978), (13311, 2113), (13719, 2134), (13746, 2139), (14011, 2173),
  (15079, 2309), (15950, 2405), (16467, 2447), (17456, 2556), (17469, 2560),
  (17489, 2563), (17571, 2603), (17785, 2639), (17787, 2640), (18247, 2686),
  (18285, 2689), (18287, 2690), (18302, 2695), (18367, 2704), (18421, 2713),
  (18432, 2716), (18434, 2717), (18443, 2720), (19338, 2775), (19382, 2781),
  (19389, 2783), (19393, 2784), (19398, 2787), (19457, 2792), (19459, 2793),
  (19468, 2797), (19469, 2799), (19480, 2807), (19486, 2810), (19491, 2813),
  (20861, 2933), (20941, 2949), (22221, 3035), (22704, 3065), (22743, 3071),
  (23011, 3099), (23128, 3122), (23171, 3128), (23772, 3192), (23917, 3214),
  (23988, 3229), (24026, 3232), (24432, 3266), (24488, 3273), (24492, 3276),
  (24508, 3279), (24568, 3294), (24582, 3299), (24622, 3303), (24624, 3304),
  (24635, 3305), (24639, 3307), (24644, 3309), (24703, 3316), (24714, 3319),
  (25577, 3378), (25594, 3382), (25660, 3389), (25664, 3391), (25669, 3392),
  (25686, 3399), (25687, 3402), (26731, 3453), (26733, 3454), (26737, 3455),
  (26742, 3460), (26748, 3461), (26753, 3462), (26823, 3470), (26824, 3472),
  (26829, 3475), (26835, 3476), (26841, 3481), (26846, 3484), (26929, 3493),
  (26931, 3494), (26935, 3496), (26940, 3498), (26946, 3504), (26947, 3506)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y0_check. -/
theorem X1Split54A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y0_pairs. -/
theorem X1Split54A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks0S256Chunk0 masks4S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks4S32768Chunk0_bound y hy)
  · exact X1Split54A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0_pairs. -/
theorem X1Split54A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split54A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0_pairs. -/
theorem X1Split54A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split54A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split54_check. -/
theorem X1Split54_check : checkSplit m4TX1 (0, 4, 4, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split54A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split55A0X0Y0Certs : List (Nat × Nat) := [
  (21, 118), (180, 326), (221, 370), (235, 379), (237, 380),
  (275, 402), (281, 409), (695, 756), (748, 787), (757, 799),
  (817, 851), (831, 861), (833, 862), (873, 875), (882, 887),
  (884, 889), (888, 891), (954, 929), (964, 946), (1786, 1594),
  (1826, 1618), (1828, 1620), (1832, 1622), (1839, 1630), (1918, 1678),
  (1924, 1696), (1930, 1703), (1941, 1722), (2926, 2590), (2980, 2625),
  (2991, 2635), (2993, 2638), (3002, 2646), (3063, 2681), (3067, 2684),
  (3072, 2688), (3073, 2692), (3084, 2708), (3089, 2712), (3178, 2770),
  (3189, 2778), (3195, 2791), (3671, 3191), (3715, 3216), (3720, 3224),
  (3790, 3264), (3792, 3265), (3801, 3272), (3809, 3293), (3813, 3298),
  (3824, 3315), (3913, 3372), (3918, 3377), (3919, 3380), (3924, 3388),
  (3925, 3396), (4007, 3446), (4016, 3452), (4022, 3466), (4028, 3492)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0Y0_check. -/
theorem X1Split55A0X0Y0_check : checkGrid m4TX1 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split55A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0Y0_pairs. -/
theorem X1Split55A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split55A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X1Split55A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0_pairs. -/
theorem X1Split55A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split55A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0_pairs. -/
theorem X1Split55A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split55A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split55_check. -/
theorem X1Split55_check : checkSplit m4TX1 (0, 5, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split55A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split56A0X0Y0Certs : List (Nat × Nat) := [
  (4, 51), (25, 152), (33, 184), (55, 307), (61, 325),
  (77, 401), (87, 452), (101, 530), (138, 743), (148, 785),
  (170, 927), (186, 1046), (206, 1196), (253, 1574), (259, 1590),
  (271, 1695), (297, 1943), (322, 2191), (351, 2583), (353, 2586),
  (363, 2631), (404, 3109), (408, 3177), (412, 3187), (424, 3290)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split56A0X0Y0_check. -/
theorem X1Split56A0X0Y0_check : checkGrid m4TX1 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split56A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split56A0X0Y0_pairs. -/
theorem X1Split56A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split56A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split56A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split56A0X0_pairs. -/
theorem X1Split56A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split56A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split56A0_pairs. -/
theorem X1Split56A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split56A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split56_check. -/
theorem X1Split56_check : checkSplit m4TX1 (0, 6, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split56A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split57A0X0Y0Certs : List (Nat × Nat) := [
  (1, 19), (3, 42), (4, 65), (5, 87), (7, 138),
  (8, 166), (9, 207), (10, 249), (13, 425), (14, 489),
  (15, 558), (16, 638), (19, 957), (20, 1102), (21, 1244),
  (22, 1392), (24, 1769), (25, 2029), (26, 2261), (28, 2859)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0X0Y0_check. -/
theorem X1Split57A0X0Y0_check : checkGrid m4TX1 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split57A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0X0Y0_pairs. -/
theorem X1Split57A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split57A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split57A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0X0_pairs. -/
theorem X1Split57A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split57A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0_pairs. -/
theorem X1Split57A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split57A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split57_check. -/
theorem X1Split57_check : checkSplit m4TX1 (0, 7, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split57A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split58A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0X0Y0_check. -/
theorem X1Split58A0X0Y0_check : checkGrid m4TX1 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split58A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0X0Y0_pairs. -/
theorem X1Split58A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 8 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split58A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split58A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0X0_pairs. -/
theorem X1Split58A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 8 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split58A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0_pairs. -/
theorem X1Split58A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 8 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split58A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split58_check. -/
theorem X1Split58_check : checkSplit m4TX1 (0, 8, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split58A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split59A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0X0Y0_check. -/
theorem X1Split59A0X0Y0_check : checkGrid m4TX1 1 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split59A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0X0Y0_pairs. -/
theorem X1Split59A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split59A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split59A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0X0_pairs. -/
theorem X1Split59A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split59A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0_pairs. -/
theorem X1Split59A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split59A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split59_check. -/
theorem X1Split59_check : checkSplit m4TX1 (1, 0, 7, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split59A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split60A0X0Y0Certs : List (Nat × Nat) := [
  (44, 1884), (56, 3132), (125, 1384), (140, 1543), (244, 2341),
  (264, 2251), (280, 2246), (295, 2564), (423, 3023), (429, 1078),
  (466, 3092), (478, 3142), (607, 2364), (615, 2008), (638, 2410),
  (652, 3100), (763, 1323), (771, 2536), (841, 1983), (859, 1386)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0X0Y0_check. -/
theorem X1Split60A0X0Y0_check : checkGrid m4TX1 1 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split60A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0X0Y0_pairs. -/
theorem X1Split60A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split60A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split60A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0X0_pairs. -/
theorem X1Split60A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split60A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0_pairs. -/
theorem X1Split60A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split60A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split60_check. -/
theorem X1Split60_check : checkSplit m4TX1 (1, 1, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split60A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split61A0X0Y0Certs : List (Nat × Nat) := [
  (457, 1038), (565, 1913), (611, 628), (626, 1936), (649, 2170),
  (653, 1881), (724, 1061), (733, 1360), (780, 1144), (1395, 2505),
  (1777, 2927), (1822, 1925), (1832, 1498), (1914, 1969), (1987, 1939),
  (2026, 1385), (2044, 2206), (2045, 2112), (2068, 2004), (2542, 2822),
  (3234, 2722), (3524, 2343), (3533, 1489), (3565, 2474), (3714, 2106),
  (3765, 291), (3821, 2214), (3824, 3032), (3859, 2339), (3872, 2954),
  (3941, 2520), (4024, 1074), (4038, 2247), (4095, 2009), (4109, 2492),
  (4198, 2215), (4262, 2254), (4302, 3135), (4303, 3034), (4778, 3257),
  (5931, 3327), (6122, 1076), (6198, 722), (6209, 1082), (6224, 2477),
  (6274, 2468), (6288, 1333), (6326, 3146), (6371, 2486), (6422, 3024),
  (6606, 3116), (6613, 1004), (6638, 1996), (6653, 2532), (6744, 2000),
  (6763, 3098), (6816, 2538), (6834, 2567), (6855, 3124), (7296, 1513),
  (8270, 1923), (8748, 2527), (8783, 2370), (8800, 2006), (8917, 1561),
  (8930, 2014), (8951, 2488), (8995, 2415), (9014, 1538), (9035, 2993),
  (9185, 1032), (9241, 2451), (9313, 463), (9322, 1861), (9348, 2333),
  (9359, 2412), (9380, 1953), (9473, 3121), (9528, 2990), (9711, 2481),
  (10467, 2002), (10954, 2568), (11000, 1955), (11002, 1534), (11056, 1358),
  (11080, 2528), (11154, 1959), (11176, 2417), (11225, 2531), (11273, 2557),
  (11573, 2509), (12204, 1486), (12355, 3114), (12421, 1211), (12424, 2553),
  (12472, 1963), (12488, 3102), (12501, 1553), (12562, 1984), (12563, 1875)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split61A0X0Y0_check. -/
theorem X1Split61A0X0Y0_check : checkGrid m4TX1 1 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split61A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split61A0X0Y0_pairs. -/
theorem X1Split61A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split61A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split61A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split61A0X0_pairs. -/
theorem X1Split61A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split61A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split61A0_pairs. -/
theorem X1Split61A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split61A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split61_check. -/
theorem X1Split61_check : checkSplit m4TX1 (1, 2, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split61A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split62A0X0Y0Certs : List (Nat × Nat) := [
  (4177, 3095), (4357, 1013), (4449, 1367), (5162, 1848), (5576, 1485),
  (6256, 461), (6265, 630), (6367, 2236), (6441, 2205), (6470, 3139),
  (6598, 2331), (6752, 508), (6965, 2198), (6984, 2534), (7516, 2285),
  (12944, 2295), (16796, 2935), (17258, 1882), (17394, 1158), (17467, 2096),
  (18273, 1059), (18377, 288), (18387, 1388), (18475, 2473), (18514, 1212),
  (19529, 981), (19556, 2926), (19566, 3120), (19694, 3134), (19736, 2299),
  (19854, 1029), (22193, 2021), (30374, 478), (32893, 2938), (33034, 2366),
  (33071, 1461), (33150, 1081), (33564, 1880), (33624, 3012), (34153, 2427),
  (34250, 1846), (34536, 284), (34612, 1058), (34888, 3068), (35318, 2107),
  (35319, 1210), (35371, 3140), (36078, 1031), (36548, 2465), (36648, 1966),
  (36695, 1823), (37039, 1072), (37129, 535), (37153, 595), (37542, 1909),
  (37964, 719), (38076, 1175), (38104, 2253), (38650, 1837), (38693, 1500),
  (38894, 2132), (39026, 3004), (39419, 2216), (43762, 2673), (55999, 1096),
  (57243, 712), (58109, 1191), (58183, 1424), (58194, 1965), (58374, 1328),
  (58478, 2431), (58600, 2013), (59090, 1497), (59165, 1279), (59523, 3026),
  (59536, 2213), (59690, 2090), (59741, 1172), (60333, 1807), (60449, 1911),
  (60948, 3123), (61009, 2407), (61440, 2165), (61564, 698), (61963, 1042),
  (62062, 1557), (62349, 1998), (62535, 1207), (62548, 2495), (62574, 1322),
  (63025, 1886), (63432, 2152), (63585, 3111), (64311, 3062), (64473, 2178),
  (68951, 3361), (80797, 1918), (81342, 2354), (81508, 2143), (81515, 510),
  (81597, 1921), (82219, 2414), (82390, 3145), (82452, 1544), (82744, 2491),
  (83691, 1452), (83746, 2182), (83921, 2374), (84003, 2130), (84081, 2994),
  (84490, 2147), (84563, 527), (85320, 2956), (85598, 993), (85802, 1874),
  (86312, 238), (86523, 1552), (86774, 2889), (86781, 2436), (87009, 1523),
  (87018, 1949), (87481, 1935), (87642, 2494), (88059, 2209), (88077, 2329),
  (88111, 1378), (88865, 3090), (90196, 2469), (97628, 1975), (101633, 1958),
  (101664, 3084), (102142, 1208), (102551, 3075), (102564, 1162), (102582, 1193),
  (102741, 1981), (103054, 1422), (103654, 1952), (103930, 2952), (103976, 3060),
  (104023, 2565), (104125, 2550), (105080, 2418), (105122, 3003), (106285, 2421),
  (113747, 2174), (114007, 2989), (114292, 1459), (114359, 3059), (115343, 1141),
  (115400, 2210), (115884, 2925), (115903, 2136), (115928, 2185), (116186, 2332),
  (116334, 2342), (117000, 1989), (117128, 3113), (117203, 1314), (117242, 1870)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0Y0_check. -/
theorem X1Split62A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split62A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0Y0_pairs. -/
theorem X1Split62A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split62A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S256Chunk0 masks3S4096Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact X1Split62A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0_pairs. -/
theorem X1Split62A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split62A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0_pairs. -/
theorem X1Split62A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split62A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split62_check. -/
theorem X1Split62_check : checkSplit m4TX1 (1, 3, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split62A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split63A0X0Y0Certs : List (Nat × Nat) := [
  (1924, 1697), (3067, 2685), (3655, 3178), (4177, 234), (4449, 509),
  (4619, 627), (4738, 720), (5061, 992), (5237, 1134), (5334, 1209),
  (5504, 1321), (5730, 1484), (5800, 1533), (5815, 1550), (5818, 1554),
  (6110, 1802), (6213, 1871), (6490, 2109), (6667, 2278), (6673, 2284),
  (6739, 2326), (6741, 2327), (6974, 2551), (6981, 2558), (7343, 2876),
  (7417, 2920), (8302, 328), (11046, 2589), (12039, 3381), (14804, 2294),
  (16338, 221), (16356, 232), (16386, 276), (16574, 469), (16796, 623),
  (17223, 982), (17235, 987), (17244, 994), (17467, 1161), (17676, 1320),
  (17779, 1383), (17888, 1467), (18009, 1559), (18364, 1847), (18649, 2098),
  (18791, 2211), (18886, 2306), (18932, 2348), (19087, 2472), (19156, 2552),
  (19527, 2883), (19711, 2999), (19763, 3028), (22374, 1818), (25112, 791),
  (27449, 2711), (28031, 3190), (28732, 449), (32806, 457), (32893, 534),
  (33020, 607), (33492, 1002), (33534, 1030), (33624, 1116), (33664, 1137),
  (33909, 1311), (33935, 1327), (34112, 1457), (34517, 1796), (34603, 1845),
  (34613, 1855), (34629, 1866), (34632, 1869), (34904, 2105), (34913, 2111),
  (35128, 2307), (35283, 2430), (35928, 2983), (35930, 2984), (36047, 3055),
  (36076, 3086), (36692, 282), (37049, 598), (37095, 620), (37114, 654),
  (37188, 699), (37636, 1071), (37694, 1121), (37788, 1185), (37877, 1262),
  (38076, 1377), (38618, 1825), (38652, 1838), (38668, 1849), (38893, 2073),
  (39026, 2135), (39117, 2233), (39357, 2440), (39376, 2457), (39379, 2461),
  (39417, 2513), (40035, 3009), (40052, 3020), (40166, 3143), (41208, 676),
  (45623, 940), (46499, 1629), (48375, 3217), (49001, 408), (50656, 1711),
  (52510, 3263), (53837, 1035), (56984, 275), (57426, 660), (57923, 1052),
  (58072, 1169), (58074, 1170), (58109, 1206), (58201, 1276), (58209, 1284),
  (58354, 1350), (58426, 1433), (58428, 1434), (58474, 1458), (58896, 1808),
  (58899, 1809), (58982, 1859), (59048, 1910), (59165, 2058), (59259, 2101),
  (59316, 2126), (59634, 2425), (60356, 3022), (60366, 3033), (60424, 3076),
  (60919, 97), (60991, 218), (61197, 440), (61384, 587), (61560, 709),
  (61568, 716), (61992, 1066), (62214, 1227), (62365, 1334), (62435, 1373),
  (62494, 1437), (62627, 1524), (63168, 1994), (63254, 2074), (63417, 2169),
  (63432, 2194), (63550, 2310), (63553, 2314), (63596, 2350), (64185, 2878),
  (64209, 2895), (64310, 2962), (64473, 3066), (66627, 1481), (69777, 798),
  (70927, 1669), (72104, 2707), (74044, 945), (74908, 1619), (76158, 2702),
  (79351, 1917), (81586, 506), (81603, 525), (81645, 551), (81677, 581),
  (81845, 697), (82704, 1348), (82828, 1451), (83396, 1905), (83398, 1906),
  (83449, 1956), (83541, 2069), (83694, 2144), (83697, 2145), (83746, 2208),
  (83913, 2363), (83924, 2375), (83927, 2376), (83997, 2426), (84084, 2516),
  (84563, 2924), (84575, 2934), (84706, 3015), (84762, 3053), (85320, 176),
  (85379, 236), (85423, 289), (85677, 536), (85755, 594), (85870, 679),
  (85916, 706), (86278, 1010), (86450, 1142), (86685, 1308), (86998, 1532),
  (87005, 1539), (87011, 1547), (87017, 1551), (87522, 1980), (87771, 2164),
  (87843, 2235), (87995, 2380), (88034, 2399), (88158, 2537), (88615, 2919),
  (88671, 2963), (88865, 3110), (92164, 2464), (95321, 1721), (96560, 2771),
  (97100, 3223), (99698, 1974), (101877, 503), (102091, 663), (102582, 1050),
  (102722, 1155), (102739, 1173), (102752, 1188), (102818, 1231), (102834, 1260),
  (102912, 1301), (102926, 1309), (103081, 1430), (103123, 1450), (103224, 1522),
  (103533, 1790), (103546, 1800), (103548, 1801), (103829, 2060), (103883, 2087),
  (104287, 2416), (104891, 2953), (105085, 3077), (105089, 3080), (105122, 3137),
  (108336, 2401), (110493, 874), (112798, 2769), (113631, 3449), (113722, 153),
  (113747, 185), (113788, 226), (113975, 435), (113990, 447), (114686, 1000),
  (114866, 1140), (114872, 1143), (115138, 1329), (115318, 1460), (115928, 1951),
  (115940, 1977), (116160, 2128), (116184, 2148), (116203, 2179), (116269, 2240),
  (116395, 2365), (116461, 2406), (116575, 2529), (117051, 2932), (117069, 2950),
  (117135, 2986), (117137, 2988), (118435, 755), (121471, 3231), (121747, 3445)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0Y0_check. -/
theorem X1Split63A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split63A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0Y0_pairs. -/
theorem X1Split63A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks1S256Chunk0 masks3S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split63A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S256Chunk0 masks3S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S4096Chunk0_bound y hy)
  · exact X1Split63A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0_pairs. -/
theorem X1Split63A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split63A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0_pairs. -/
theorem X1Split63A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split63A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split63_check. -/
theorem X1Split63_check : checkSplit m4TX1 (1, 4, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split63A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split64A0X0Y0Certs : List (Nat × Nat) := [
  (55, 308), (165, 886), (270, 1668), (429, 3369), (460, 150),
  (461, 156), (468, 182), (535, 521), (553, 606), (565, 672),
  (615, 998), (749, 2092), (816, 2868), (1008, 742), (1023, 841),
  (1232, 2624), (1244, 2768), (1775, 188), (1827, 454), (1828, 465),
  (1841, 528), (1945, 1181), (1969, 1346), (1987, 1475), (2031, 1852),
  (2138, 2996), (2611, 37), (2869, 1593), (3033, 3260), (3043, 3443),
  (3484, 53), (3528, 258), (3565, 443), (3581, 531), (3589, 573),
  (3674, 1117), (3695, 1265), (3731, 1529), (3796, 2103), (4019, 545),
  (4101, 1045), (4102, 1063), (4121, 1197), (4128, 1257), (4192, 1779),
  (4223, 2059), (4236, 2162), (4262, 2454), (4802, 115), (4840, 306),
  (4944, 858), (5218, 3441), (5237, 116), (5484, 1616), (5583, 2634),
  (5637, 3210), (6115, 149), (6136, 251), (6217, 659), (6274, 1025),
  (6296, 1199), (6309, 1283), (6399, 2064), (6440, 2545), (6490, 3017),
  (6534, 76), (6547, 142), (6734, 1223), (6822, 1942), (6823, 1971),
  (6847, 2192), (6855, 2281), (6904, 2864), (6917, 2929), (7461, 363),
  (7467, 376), (7533, 739), (7812, 3211), (7902, 378), (7977, 774),
  (8198, 2678), (8254, 3288), (8787, 453), (8806, 568), (8824, 650),
  (8944, 1447), (8995, 1903), (9022, 2190), (9033, 2296), (9083, 2881),
  (9093, 2943), (9139, 52), (9167, 179), (9178, 225), (9185, 264),
  (9217, 432), (9333, 1130), (9459, 2230), (9463, 2275), (9539, 3108),
  (10152, 775), (10160, 849), (10170, 885), (10264, 1589), (10928, 281),
  (10971, 501), (11061, 1048), (11089, 1261), (11093, 1273), (11115, 1428),
  (11154, 1786), (11219, 2395), (11279, 3107), (11760, 113), (11898, 842),
  (12015, 1666), (12108, 2630), (12204, 147), (12213, 183), (12217, 208),
  (12272, 493), (12314, 703), (12380, 1139), (12461, 1793), (12477, 1944),
  (12520, 2361), (12616, 35), (12683, 369), (12989, 2766), (13039, 3287)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0X0Y0_check. -/
theorem X1Split64A0X0Y0_check : checkGrid m4TX1 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0X0Y0_pairs. -/
theorem X1Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split64A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0X0_pairs. -/
theorem X1Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0_pairs. -/
theorem X1Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split64_check. -/
theorem X1Split64_check : checkSplit m4TX1 (1, 5, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split65A0X0Y0Certs : List (Nat × Nat) := [
  (2, 32), (17, 734), (27, 2578), (39, 201), (43, 418),
  (66, 100), (83, 1562), (89, 3160), (135, 563), (139, 963),
  (191, 297), (192, 357), (207, 2571), (256, 640), (260, 1105),
  (291, 1243), (294, 1770), (332, 34), (342, 361), (347, 729),
  (377, 730), (378, 838), (389, 3165), (442, 1398), (445, 2033),
  (451, 18), (453, 43), (516, 98), (528, 839), (533, 1563),
  (540, 9), (551, 303), (563, 1571), (626, 2262), (628, 2858),
  (634, 66), (637, 131), (690, 10), (702, 353), (717, 2576),
  (755, 88), (758, 162), (812, 25), (828, 833), (839, 3170),
  (850, 247), (854, 486), (870, 8), (876, 104), (881, 301)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0X0Y0_check. -/
theorem X1Split65A0X0Y0_check : checkGrid m4TX1 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0X0Y0_pairs. -/
theorem X1Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split65A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0X0_pairs. -/
theorem X1Split65A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0_pairs. -/
theorem X1Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split65_check. -/
theorem X1Split65_check : checkSplit m4TX1 (1, 6, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0X0Y0_check. -/
theorem X1Split66A0X0Y0_check : checkGrid m4TX1 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0X0Y0_pairs. -/
theorem X1Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split66A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0X0_pairs. -/
theorem X1Split66A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0_pairs. -/
theorem X1Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split66_check. -/
theorem X1Split66_check : checkSplit m4TX1 (1, 7, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split67A0X0Y0Certs : List (Nat × Nat) := [
  (39, 3418), (112, 1726), (172, 3503), (195, 2847), (223, 2796),
  (239, 2734), (280, 3489), (310, 3269), (339, 3410), (394, 1642)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0X0Y0_check. -/
theorem X1Split67A0X0Y0_check : checkGrid m4TX1 1 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0X0Y0_pairs. -/
theorem X1Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split67A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0X0_pairs. -/
theorem X1Split67A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0_pairs. -/
theorem X1Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split67_check. -/
theorem X1Split67_check : checkSplit m4TX1 (2, 0, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split67A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split68A0X0Y0Certs : List (Nat × Nat) := [
  (229, 1387), (236, 1495), (985, 2562), (1126, 2160), (1172, 2827),
  (1176, 2826), (1193, 1900), (1199, 3416), (1205, 2487), (1224, 2252),
  (1327, 2001), (2775, 1916), (2992, 3101), (2994, 1079), (3028, 3127),
  (3185, 619), (3292, 3105), (3366, 3495), (3371, 801), (3372, 3295),
  (3387, 1676), (3416, 3031), (3423, 3048), (3430, 2530), (3583, 2463),
  (5160, 806), (5171, 3483), (5178, 3283), (5183, 2812), (5740, 2413),
  (5841, 1968), (5856, 3437), (5867, 2321), (5868, 2507), (5873, 3517),
  (5953, 1502), (6123, 2010), (6146, 3138), (6158, 1054), (6343, 629),
  (6352, 1332), (6430, 1372), (6549, 1034), (6596, 3052), (6702, 3457),
  (6707, 1729), (6708, 333), (6719, 2786), (6725, 2467), (6757, 237),
  (6766, 1858), (6919, 2369), (7170, 3405), (7176, 3258), (7181, 2804),
  (7199, 2727), (8400, 1736), (8402, 1735), (8417, 3326), (8427, 3488),
  (9054, 1354), (9136, 1938), (9243, 2072), (9271, 2199), (9300, 2773),
  (9312, 1624), (9323, 950), (9327, 3320), (9439, 2498), (9605, 2442),
  (9607, 2541), (9644, 1960), (10172, 2765), (10181, 3354), (10182, 1514),
  (10187, 3511), (11390, 1542), (11463, 1922), (11596, 2157), (11599, 2928),
  (11632, 2241), (11767, 2961), (11794, 3125), (11822, 3451), (11838, 2696),
  (11847, 1716), (11849, 1684), (11964, 2449), (12100, 1178), (12103, 2547)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0X0Y0_check. -/
theorem X1Split68A0X0Y0_check : checkGrid m4TX1 1 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0X0Y0_pairs. -/
theorem X1Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split68A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0X0_pairs. -/
theorem X1Split68A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0_pairs. -/
theorem X1Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split68_check. -/
theorem X1Split68_check : checkSplit m4TX1 (2, 1, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split68A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split69A0X0Y0Certs : List (Nat × Nat) := [
  (3069, 1494), (3133, 1374), (3337, 1964), (4465, 1088), (4479, 826),
  (4480, 2480), (7830, 2042), (8762, 1128), (8843, 2817), (10696, 3038),
  (12628, 2540), (12835, 1986), (12930, 3013), (13000, 2402), (14100, 1976),
  (14115, 2428), (14307, 3115), (16294, 1957), (16966, 3415), (17033, 3513),
  (17042, 1896), (17101, 2023), (17120, 1828), (17224, 3512), (17236, 2828),
  (17327, 3420), (17339, 1890), (17398, 3419), (17485, 2484), (17587, 2184),
  (17634, 2124), (19222, 1839), (19387, 1930), (19445, 2131), (20671, 2025),
  (20691, 1764), (20692, 2508), (21770, 1312), (25315, 1920), (25433, 1164),
  (25537, 2196), (31763, 2886), (33209, 2088), (33326, 3515), (37333, 2615),
  (40059, 1813), (40250, 1954), (40271, 2411), (41377, 2514), (41411, 1819),
  (41446, 2351), (41724, 1519), (43115, 1075), (43192, 3087), (43403, 3133),
  (43613, 462), (43791, 2302), (43810, 2108), (46139, 2335), (47730, 1326),
  (48735, 758), (48737, 406), (48879, 3275), (48890, 382), (48975, 2682),
  (49071, 3448), (49083, 3219), (49137, 318), (49143, 2779), (49153, 1631),
  (49179, 3029), (49330, 2311), (49538, 3057), (49774, 2521), (49888, 3007),
  (49922, 3050), (51945, 1073), (52112, 2070), (52153, 3061), (55042, 2669),
  (55156, 2850), (55157, 2821), (56626, 1179), (62389, 1979), (62524, 2138),
  (62596, 3117), (72252, 394), (73787, 2991), (73885, 3526), (74502, 918),
  (74875, 1731), (74881, 805), (74967, 3241), (74975, 2802), (74979, 2723),
  (74985, 1646), (75090, 1647), (75173, 905), (75188, 3386), (75238, 2654),
  (79507, 3516), (79513, 2272), (80459, 3249), (83193, 1503), (83219, 2379),
  (83269, 2353), (84502, 612), (84691, 1201), (84740, 1932), (84882, 3434),
  (84891, 2390), (84897, 2503), (84972, 2506), (84990, 3438), (85084, 2393),
  (85176, 3440), (85193, 2392), (85237, 3436), (85248, 2386), (86329, 3144),
  (86594, 2522), (86698, 277), (86750, 682), (86800, 1159), (88870, 2005),
  (88916, 1468), (88984, 3082), (89388, 609), (89399, 1060), (89569, 3027),
  (91811, 621), (91966, 1057), (92064, 1878), (93185, 1053), (94949, 1051),
  (94964, 2466), (95110, 2400), (95664, 1418), (97071, 1683), (97073, 1636),
  (97077, 936), (97152, 763), (97258, 894), (97269, 3468), (97362, 3374),
  (97413, 3220), (97422, 2709), (97429, 802), (97493, 1436), (97525, 2462),
  (97725, 683), (97958, 460), (98170, 1012), (98203, 233), (100178, 1907),
  (100341, 1999), (100380, 2955), (100860, 1898), (100915, 1892), (103966, 2728),
  (103982, 2790), (104020, 3252), (104033, 921), (104113, 3387), (104218, 1662),
  (104334, 1665), (104388, 689), (104394, 3465), (104398, 2674), (105646, 3514),
  (105716, 3414), (106034, 3356), (106035, 3255), (107614, 2158)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X0Y0_check. -/
theorem X1Split69A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X0Y0_pairs. -/
theorem X1Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X0_pairs. -/
theorem X1Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split69A0X1Y0Certs : List (Nat × Nat) := [
  (45, 782), (47, 398), (933, 817), (4529, 479), (4645, 2320),
  (4752, 3070), (9798, 1382), (10298, 2189), (10455, 3509), (10506, 3331),
  (10578, 2815), (10588, 1734), (10593, 2739), (10604, 3329), (10710, 1095),
  (10814, 2740), (10852, 1022), (10869, 2738), (16105, 127), (16253, 3215),
  (17147, 1376), (19625, 1351), (19788, 2441), (19820, 1843), (21097, 2499),
  (21131, 1536), (21175, 1195), (22649, 1937), (23278, 1359), (23437, 2200),
  (23438, 2110), (23567, 899), (23632, 407), (23643, 778), (23645, 383),
  (23655, 2687), (23754, 1672), (23760, 2683), (23853, 1702), (23898, 2780),
  (23919, 856), (25545, 2923), (25760, 1136), (25915, 700), (25961, 1501),
  (25999, 2133), (28087, 2526), (28126, 2443), (28184, 3010), (28297, 1353),
  (28466, 1967), (28514, 2419), (30943, 1690), (31294, 910), (32517, 2951),
  (36122, 3362), (36177, 3491), (36243, 1444), (36264, 1443), (36369, 1511),
  (36376, 2762), (36458, 2760), (36467, 3365), (36511, 2764), (36522, 3363),
  (37844, 3523), (37886, 2345), (37894, 348), (37895, 1492), (39816, 3078),
  (44492, 1692), (44496, 924), (45825, 1752), (49621, 2391), (49869, 906),
  (49880, 1097), (53587, 1919), (53809, 2195), (53844, 1997), (54832, 988),
  (54940, 1912), (55155, 1157), (56598, 2149), (56788, 2204), (56880, 2338),
  (57064, 2458), (57264, 2187), (57335, 2555), (59255, 2212), (59639, 3126),
  (59648, 3030), (59767, 1995), (60031, 1677), (60045, 896), (60091, 3469),
  (60183, 3384), (60200, 938), (60295, 939), (60392, 271), (60398, 2777),
  (60404, 3376), (60454, 2618), (62169, 1043), (62315, 3063), (62404, 2100),
  (62508, 2496), (62554, 1525), (64068, 1204), (64226, 1174), (64292, 1421),
  (71142, 2819), (71148, 1558), (72483, 2816), (75714, 1036), (75788, 512),
  (75883, 1934)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X1Y0_check. -/
theorem X1Split69A0X1Y0_check : checkGrid m4TX1 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X1Y0_pairs. -/
theorem X1Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X1_pairs. -/
theorem X1Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0_pairs. -/
theorem X1Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split69A0X0_pairs x hx y hy hw
  · exact X1Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split69_check. -/
theorem X1Split69_check : checkSplit m4TX1 (2, 2, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split69A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y0Certs : List (Nat × Nat) := [
  (15012, 290), (16465, 195), (20881, 523), (20949, 575), (30140, 550),
  (35604, 403), (40220, 413), (47514, 533), (51651, 555), (51688, 589),
  (55939, 267), (57567, 372), (73299, 197), (88365, 442), (99487, 287),
  (101819, 549), (105356, 517), (111750, 268), (114364, 332), (114417, 386),
  (118161, 524), (118246, 588)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y0_check. -/
theorem X1Split70A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y0_pairs. -/
theorem X1Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X1Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y1Certs : List (Nat × Nat) := [
  (5412, 822), (16413, 610), (19024, 664), (22659, 696), (47206, 681),
  (48807, 721), (50777, 668), (54777, 1008), (57517, 746), (57666, 864),
  (57706, 876), (58326, 979), (61057, 693), (82364, 932), (87597, 625),
  (88310, 803), (88316, 804), (88448, 904), (89031, 954), (97921, 694),
  (112225, 678), (114365, 762), (114503, 866), (114542, 880), (114780, 671),
  (115354, 715), (115688, 991), (122473, 685), (122484, 687), (122662, 823)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y1_check. -/
theorem X1Split70A0X0Y1_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y1_pairs. -/
theorem X1Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X1Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y2Certs : List (Nat × Nat) := [
  (3781, 1154), (3922, 1277), (5567, 1337), (14986, 1127), (16585, 1156),
  (23028, 1366), (51342, 1129), (51691, 1355), (58593, 1187), (58728, 1290),
  (61266, 1278), (67249, 1149), (73509, 1229), (99568, 1203), (99663, 1275),
  (101446, 1069), (104596, 1131), (105262, 1237), (105367, 1313), (109596, 1028),
  (111680, 1056), (111955, 1281), (112122, 1368)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y2_check. -/
theorem X1Split70A0X0Y2_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y2_pairs. -/
theorem X1Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X1Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y3Certs : List (Nat × Nat) := [
  (19029, 1448), (24345, 1612), (24539, 1758), (40207, 1607), (47606, 1797),
  (54405, 1482), (55912, 1462), (57582, 1584), (57597, 1596), (61113, 1520),
  (85271, 1609), (88379, 1645), (97915, 1473), (99467, 1499), (102122, 1560),
  (104567, 1470), (108250, 1549), (112156, 1417), (114438, 1602), (114473, 1625),
  (114705, 1413), (117942, 1517), (122725, 1661), (122734, 1663), (122772, 1720)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y3_check. -/
theorem X1Split70A0X0Y3_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y3_pairs. -/
theorem X1Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X1Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y4Certs : List (Nat × Nat) := [
  (9524, 2076), (9722, 2223), (19101, 1908), (19999, 1827), (20012, 1830),
  (20082, 1889), (20103, 1895), (20114, 1899), (20910, 2127), (22556, 1821),
  (22955, 2125), (47310, 1962), (47477, 2104), (48974, 2086), (50862, 1931),
  (51636, 2129), (54739, 2166), (55907, 1865), (58208, 2095), (61217, 2068),
  (98262, 2172), (99584, 2044), (104794, 2093), (105127, 1929), (105300, 2091),
  (108106, 1842), (109671, 1867), (111982, 2099), (112187, 1835), (114716, 1822),
  (114972, 2062), (115671, 2177), (124162, 2048), (124226, 2081), (127376, 2119)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y4_check. -/
theorem X1Split70A0X0Y4_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y4_pairs. -/
theorem X1Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X1Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y5Certs : List (Nat × Nat) := [
  (3661, 2301), (16518, 2349), (19199, 2438), (35695, 2592), (54397, 2330),
  (56026, 2404), (58188, 2525), (65001, 2670), (88036, 2665), (88519, 2655),
  (89048, 2662), (97884, 2312), (99935, 2317), (99946, 2319), (100018, 2383),
  (100145, 2504), (101654, 2459), (109854, 2470), (111828, 2398), (112373, 2432),
  (114564, 2608), (114614, 2642), (118092, 2524), (122865, 2675)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y5_check. -/
theorem X1Split70A0X0Y5_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y5_pairs. -/
theorem X1Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X1Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y6Certs : List (Nat × Nat) := [
  (20103, 2820), (20108, 2823), (20115, 2825), (22838, 2945), (29905, 2872),
  (37720, 2965), (47533, 3011), (50984, 2930), (51433, 2894), (58109, 2906),
  (58251, 2998), (58861, 3054), (61417, 3051), (64705, 2843), (67115, 2743),
  (88066, 2699), (98096, 2937), (99767, 3019), (100035, 2845), (100036, 2846),
  (101859, 3046), (102272, 2987), (105459, 3058), (108342, 2944), (109818, 2904),
  (115097, 3002), (118073, 2948)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y6_check. -/
theorem X1Split70A0X0Y6_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y6_pairs. -/
theorem X1Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X1Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y7Certs : List (Nat × Nat) := [
  (15245, 3094), (15258, 3119), (18922, 3417), (34795, 3153), (53385, 3180),
  (53451, 3225), (53521, 3267), (76249, 3194), (79130, 3207), (82026, 3239),
  (82108, 3311), (93217, 3433), (93227, 3435), (93238, 3439), (113986, 3285),
  (114003, 3314), (115953, 3342), (115978, 3358), (118420, 3424)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y7_check. -/
theorem X1Split70A0X0Y7_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y7_pairs. -/
theorem X1Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X1Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0_pairs. -/
theorem X1Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split70A0X0Y0_pairs x hx y hy hw
  · exact X1Split70A0X0Y1_pairs x hx y hy hw
  · exact X1Split70A0X0Y2_pairs x hx y hy hw
  · exact X1Split70A0X0Y3_pairs x hx y hy hw
  · exact X1Split70A0X0Y4_pairs x hx y hy hw
  · exact X1Split70A0X0Y5_pairs x hx y hy hw
  · exact X1Split70A0X0Y6_pairs x hx y hy hw
  · exact X1Split70A0X0Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y0Certs : List (Nat × Nat) := [
  (1507, 586), (1513, 590), (5574, 556), (27507, 500), (27833, 331),
  (29776, 194), (44755, 344), (63364, 507), (70474, 459), (70791, 270),
  (70868, 345), (73153, 553), (89165, 192)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y0_check. -/
theorem X1Split70A0X1Y0_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y0_pairs. -/
theorem X1Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X1Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y1Certs : List (Nat × Nat) := [
  (12760, 984), (24707, 695), (27296, 717), (27828, 752), (27964, 855),
  (28012, 877), (51442, 794), (64547, 616), (64982, 980), (70183, 618),
  (70869, 771), (70900, 797), (73211, 1011)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y1_check. -/
theorem X1Split70A0X1Y1_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y1_pairs. -/
theorem X1Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y1Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X1Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y2Certs : List (Nat × Nat) := [
  (12288, 1017), (12301, 1021), (12310, 1023), (23265, 1186), (23390, 1285),
  (23444, 1310), (24805, 1190), (26924, 1232), (29987, 1228), (33496, 1176),
  (33517, 1200), (54159, 1306), (54169, 1315), (58673, 1239), (64707, 1153),
  (67220, 1132), (69973, 1282), (70300, 1135), (73616, 1307), (85124, 1124),
  (85262, 1220)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y2_check. -/
theorem X1Split70A0X1Y2_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y2_pairs. -/
theorem X1Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y2Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X1Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y3Certs : List (Nat × Nat) := [
  (11265, 1380), (12696, 1732), (12706, 1733), (13757, 1748), (23057, 1412),
  (24758, 1518), (26654, 1420), (27903, 1597), (42555, 1440), (42642, 1507),
  (42659, 1509), (42973, 1760), (42974, 1761), (67257, 1521), (69759, 1479),
  (70371, 1555), (70942, 1613), (75279, 1411), (82322, 1718)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y3_check. -/
theorem X1Split70A0X1Y3_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y3_pairs. -/
theorem X1Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y3Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X1Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y4Certs : List (Nat × Nat) := [
  (26730, 1872), (27628, 2202), (29913, 1991), (30297, 1857), (33120, 2094),
  (33287, 1806), (33541, 2049), (63191, 1985), (63433, 2155), (63463, 2197),
  (64983, 2176), (67030, 2171), (67335, 2052), (67548, 2181), (75602, 2089)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y4_check. -/
theorem X1Split70A0X1Y4_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y4_pairs. -/
theorem X1Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y4Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X1Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y5Certs : List (Nat × Nat) := [
  (5148, 2238), (23369, 2518), (24846, 2448), (27220, 2303), (27428, 2493),
  (28073, 2626), (29819, 2328), (30549, 2546), (33034, 2445), (33317, 2249),
  (44700, 2367), (51593, 2610), (64604, 2313), (66649, 2308), (67401, 2519),
  (69667, 2242), (69760, 2337), (70195, 2283), (71086, 2629), (71097, 2645),
  (72729, 2237), (72867, 2373), (89104, 2232)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y5_check. -/
theorem X1Split70A0X1Y5_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y5_pairs. -/
theorem X1Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y5Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X1Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y6Certs : List (Nat × Nat) := [
  (12318, 2737), (24872, 2931), (26936, 2946), (27365, 2888), (27659, 2706),
  (33169, 3000), (33671, 2995), (42580, 2758), (42586, 2759), (42597, 2761),
  (44274, 2899), (44398, 2974), (47369, 2910), (47579, 3044), (58728, 2973),
  (63184, 2871), (63223, 2900), (66949, 2992), (73434, 2884), (75673, 3001)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y6_check. -/
theorem X1Split70A0X1Y6_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y6_pairs. -/
theorem X1Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y6Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X1Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y7Certs : List (Nat × Nat) := [
  (10772, 3349), (11683, 3330), (11766, 3409), (12662, 3344), (25784, 3184),
  (26032, 3371), (39827, 3364), (65244, 3129), (65803, 3209), (65904, 3271),
  (76323, 3243)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y7_check. -/
theorem X1Split70A0X1Y7_check : checkGrid m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y7_pairs. -/
theorem X1Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y7Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X1Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1_pairs. -/
theorem X1Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split70A0X1Y0_pairs x hx y hy hw
  · exact X1Split70A0X1Y1_pairs x hx y hy hw
  · exact X1Split70A0X1Y2_pairs x hx y hy hw
  · exact X1Split70A0X1Y3_pairs x hx y hy hw
  · exact X1Split70A0X1Y4_pairs x hx y hy hw
  · exact X1Split70A0X1Y5_pairs x hx y hy hw
  · exact X1Split70A0X1Y6_pairs x hx y hy hw
  · exact X1Split70A0X1Y7_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0_pairs. -/
theorem X1Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split70A0X0_pairs x hx y hy hw
  · exact X1Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split70_check. -/
theorem X1Split70_check : checkSplit m4TX1 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split71A0X0Y0Certs : List (Nat × Nat) := [
  (3077, 177), (3133, 466), (3179, 702), (3248, 1152), (4491, 750),
  (5384, 873), (5479, 1592), (5750, 499), (12667, 274), (13945, 151),
  (14005, 445), (14096, 975), (16280, 1041), (17241, 1778), (17258, 1888),
  (17264, 2015), (17500, 519), (17587, 1062), (17651, 1528), (17719, 2123),
  (19239, 513), (19265, 653), (20708, 1610), (22321, 736), (22548, 2633),
  (22819, 1133), (25235, 55), (26725, 1109), (30169, 843), (33847, 2584),
  (33968, 211), (40121, 529), (40150, 675), (40254, 1406), (41458, 691),
  (43147, 433), (43157, 494), (43192, 658), (43194, 666), (43587, 455),
  (43684, 1024), (43786, 1814), (46495, 2887), (47711, 1928), (48725, 56),
  (48976, 1583), (49074, 2594), (49329, 971), (49380, 1318), (49795, 1182),
  (49888, 1970), (49940, 2544), (49992, 3045), (51969, 1168), (52006, 1432),
  (55177, 2667), (57192, 1216), (57675, 1578), (57844, 3286), (58170, 2097),
  (60724, 1591), (60871, 3172), (62232, 159), (64682, 2041), (69606, 68),
  (74360, 3181), (74909, 471), (74910, 474), (75239, 3236), (75366, 579),
  (83092, 73), (83166, 430), (84596, 1198), (84637, 1474), (84722, 2290),
  (85152, 2271), (85156, 2286), (85161, 2316), (86365, 1409), (86815, 1515),
  (88920, 999), (88934, 1119), (88984, 1445), (88986, 1466), (89298, 646),
  (89361, 1047), (89470, 1902), (91811, 157), (91838, 278), (91883, 505),
  (92164, 2862), (93176, 451), (94863, 181), (94880, 265), (95122, 1864),
  (95568, 2043), (97032, 160), (97363, 2606), (97418, 3197), (97651, 1253),
  (97723, 1799), (97906, 175), (98196, 2163), (98203, 2274), (98258, 2882),
  (100370, 2142), (100391, 2371), (104085, 643), (104134, 920), (104332, 2666),
  (106133, 3352), (108203, 2221), (108370, 305), (108672, 2599), (109149, 3005),
  (110119, 339)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X0Y0_check. -/
theorem X1Split71A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X0Y0_pairs. -/
theorem X1Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X0_pairs. -/
theorem X1Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split71A0X1Y0Certs : List (Nat × Nat) := [
  (1797, 313), (2103, 2632), (4440, 475), (6909, 2885), (10622, 1016),
  (10628, 1084), (10629, 1089), (11532, 1296), (13623, 740), (13854, 2701),
  (19811, 1410), (19978, 3072), (20920, 217), (21058, 985), (22840, 1287),
  (23138, 438), (23377, 2193), (23402, 2453), (23510, 126), (23561, 375),
  (23631, 751), (25564, 2300), (26014, 2512), (28131, 1854), (28149, 2065),
  (28184, 2394), (28186, 2437), (28513, 1415), (28554, 1785), (28572, 1941),
  (30153, 741), (30433, 3221), (36336, 1401), (36338, 1405), (36533, 3351),
  (38181, 2315), (40425, 3151), (40484, 173), (41399, 388), (42346, 813),
  (43914, 3200), (47122, 753), (47404, 3289), (49779, 1090), (53509, 50),
  (53529, 146), (53843, 2324), (55145, 2305), (55196, 2891), (56572, 140),
  (56598, 259), (56599, 260), (56768, 1274), (57099, 593), (57274, 1832),
  (59281, 644), (59776, 1007), (59925, 2280), (59999, 3106), (60106, 396),
  (60193, 871), (60293, 1611), (61880, 574), (62218, 94), (63956, 91),
  (64158, 1259), (64226, 1792), (64338, 2941), (66287, 909), (68134, 1746),
  (69702, 540), (73570, 304), (73780, 1626), (75966, 1777)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X1Y0_check. -/
theorem X1Split71A0X1Y0_check : checkGrid m4TX1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X1Y0_pairs. -/
theorem X1Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X1_pairs. -/
theorem X1Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0_pairs. -/
theorem X1Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split71A0X0_pairs x hx y hy hw
  · exact X1Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split71_check. -/
theorem X1Split71_check : checkSplit m4TX1 (2, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split72A0X0Y0Certs : List (Nat × Nat) := [
  (317, 732), (372, 356), (877, 134), (880, 248), (964, 64),
  (973, 423), (1433, 1572), (1548, 836), (1742, 24), (2774, 488),
  (2776, 637), (2863, 421), (2866, 641), (3009, 200), (3019, 966),
  (3807, 2573), (3960, 7), (4197, 2577), (4296, 102), (5840, 1101),
  (5842, 1394), (5989, 961), (5992, 1389), (6165, 562), (6174, 1767),
  (6548, 169), (6550, 246), (7319, 3166), (7472, 33), (7829, 3169),
  (7992, 352), (8633, 1564), (9295, 2031), (9296, 2257), (9474, 1774),
  (9476, 2258), (9633, 44), (9651, 1246), (9756, 99), (10301, 298),
  (10931, 292), (11118, 832), (11371, 16), (11377, 137), (11795, 84),
  (11818, 2857), (11973, 46), (11975, 83), (12767, 723), (12900, 6)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0X0Y0_check. -/
theorem X1Split72A0X0Y0_check : checkGrid m4TX1 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0X0Y0_pairs. -/
theorem X1Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split72A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0X0_pairs. -/
theorem X1Split72A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0_pairs. -/
theorem X1Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split72_check. -/
theorem X1Split72_check : checkSplit m4TX1 (2, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0X0Y0_check. -/
theorem X1Split73A0X0Y0_check : checkGrid m4TX1 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0X0Y0_pairs. -/
theorem X1Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split73A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0X0_pairs. -/
theorem X1Split73A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0_pairs. -/
theorem X1Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split73_check. -/
theorem X1Split73_check : checkSplit m4TX1 (2, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split74A0X0Y0Certs : List (Nat × Nat) := [
  (275, 2968), (332, 3510), (595, 2980), (954, 1660), (1093, 3456),
  (1356, 2803), (1644, 1715), (1786, 2757), (1832, 3527), (2264, 3281),
  (2581, 3335), (2708, 1727), (2809, 2725), (2980, 1754), (2993, 3350),
  (3073, 2977), (3324, 2083), (3792, 2835), (3813, 2078), (3925, 819)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X0Y0_check. -/
theorem X1Split74A0X0Y0_check : checkGrid m4TX1 1 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X0Y0_pairs. -/
theorem X1Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split74A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X0_pairs. -/
theorem X1Split74A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0_pairs. -/
theorem X1Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split74A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split74_check. -/
theorem X1Split74_check : checkSplit m4TX1 (3, 0, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split74A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split75A0X0Y0Certs : List (Nat × Nat) := [
  (1909, 2890), (4026, 1230), (5233, 1480), (5245, 2244), (5478, 1744),
  (9960, 1338), (9962, 1298), (9978, 3347), (11235, 2482), (11236, 1087),
  (11663, 1759), (11812, 1288), (12144, 470), (13500, 3254), (14992, 3104),
  (16482, 1762), (16627, 667), (17021, 908), (17861, 3043), (17867, 3157),
  (17879, 2972), (18432, 2239), (20201, 2976), (21709, 2460), (21718, 3049),
  (22560, 2837), (28917, 854), (32790, 1680), (32792, 1635), (32796, 934),
  (35631, 2510), (35632, 2024), (36777, 2844), (37076, 707), (37623, 1080),
  (39752, 1464), (40680, 3247), (40692, 3464), (40698, 600), (41309, 3345),
  (43227, 2663), (43496, 3021), (45635, 2352), (45828, 2848), (46033, 1469),
  (47417, 1085), (49331, 187), (49337, 2776), (49343, 3375), (50268, 2978),
  (52937, 767), (56678, 389), (56694, 2346), (57239, 223), (58082, 3529),
  (61667, 1894), (62046, 824), (67922, 2794), (67926, 2718), (67932, 1632),
  (69220, 1180), (69447, 2750), (71370, 3343), (72781, 2620), (72806, 2824),
  (74549, 3346), (74749, 2444), (74975, 1535), (75757, 2011), (77453, 1221),
  (77457, 3337), (77459, 3336), (77886, 2434), (78332, 2356), (81246, 3497),
  (81252, 3301), (81258, 2710), (81443, 2020), (82839, 1493), (82840, 2344),
  (83753, 1655), (84287, 543), (84293, 3463), (84297, 2658), (85560, 1425),
  (92346, 3458), (94623, 1094), (94634, 911), (95411, 604), (99348, 3158),
  (99496, 2159), (99603, 1817), (99731, 2227), (99747, 2121), (99749, 2118),
  (99929, 3431), (103532, 346), (104623, 2559), (104836, 3056), (105574, 3256),
  (105575, 3355), (107141, 1020), (107382, 2226), (107424, 1349), (107740, 2554),
  (109662, 3284), (111953, 888), (117937, 1873), (117950, 1234), (120347, 1344)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X0Y0_check. -/
theorem X1Split75A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X0Y0_pairs. -/
theorem X1Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split75A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X0_pairs. -/
theorem X1Split75A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0_pairs. -/
theorem X1Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split75A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split75_check. -/
theorem X1Split75_check : checkSplit m4TX1 (3, 1, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split75A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X0Y0Certs : List (Nat × Nat) := [
  (11078, 2653), (27735, 2293), (28723, 811), (41204, 2116), (73528, 154),
  (75715, 468), (77057, 2607), (77138, 1600), (79317, 1738), (79335, 3333),
  (79440, 3334), (79538, 1151), (79593, 1222), (80250, 1347), (80918, 769),
  (81067, 3230), (89064, 1255), (91500, 1217), (91770, 2749), (107764, 3328)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X0Y0_check. -/
theorem X1Split76A0X0Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X0Y0_pairs. -/
theorem X1Split76A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X0_pairs. -/
theorem X1Split76A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X1Y0Certs : List (Nat × Nat) := [
  (33207, 3340), (33219, 2756), (33225, 1747), (33330, 1751), (33466, 1297),
  (51431, 825), (59874, 1824), (64430, 441), (67477, 1743), (81197, 1831),
  (81285, 2017), (84759, 922), (89782, 1990), (97271, 2501), (99217, 261),
  (102699, 1419), (107408, 3041)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X1Y0_check. -/
theorem X1Split76A0X1Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X1Y0_pairs. -/
theorem X1Split76A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X1_pairs. -/
theorem X1Split76A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X2Y0Certs : List (Nat × Nat) := [
  (757, 2877), (15619, 2940), (16237, 1431), (23281, 2248), (24343, 3237),
  (35674, 2831), (36106, 2975), (36122, 3039), (36269, 3154), (36534, 3524),
  (36538, 2911), (46870, 2840), (46882, 2318), (53089, 1586), (53227, 3296),
  (54582, 1741), (70453, 3520), (74430, 414), (74432, 772), (84007, 458),
  (91872, 1070), (95414, 3238), (95531, 2652), (103249, 311), (104553, 2077),
  (104664, 2222), (104670, 2830), (104774, 2082), (104829, 2122), (105707, 1783),
  (107916, 915), (107922, 1658), (109576, 3130)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X2Y0_check. -/
theorem X1Split76A0X2Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X2Y0_pairs. -/
theorem X1Split76A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk2 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X2_pairs. -/
theorem X1Split76A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X3Y0Certs : List (Nat × Nat) := [
  (9089, 3519), (9101, 3040), (10821, 123), (14991, 3422), (15063, 2224),
  (36377, 1098), (36530, 3323), (60432, 1992), (83951, 3428), (84826, 789),
  (84840, 1701), (84891, 2597), (84978, 3182), (85199, 3226), (97182, 387),
  (104556, 1065)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X3Y0_check. -/
theorem X1Split76A0X3Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X3Y0_pairs. -/
theorem X1Split76A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk3 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X3_pairs. -/
theorem X1Split76A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X4Y0Certs : List (Nat × Nat) := [
  (10870, 3324), (30072, 852), (30081, 3174), (30168, 2591), (30285, 315),
  (30389, 2637), (42661, 2384), (44846, 554), (55150, 2967), (66774, 1471),
  (69998, 2137), (71111, 1763), (75799, 572), (91809, 705), (99895, 1049),
  (100180, 1014), (105403, 2836)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X4Y0_check. -/
theorem X1Split76A0X4Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X4Y0_pairs. -/
theorem X1Split76A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk4 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X4_pairs. -/
theorem X1Split76A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X5Y0Certs : List (Nat × Nat) := [
  (14494, 931), (14764, 2595), (19981, 1456), (33128, 1659), (33132, 953),
  (33207, 816), (33429, 913), (33477, 2726), (38068, 1068), (39430, 2372),
  (41200, 2063), (42117, 2753), (57065, 2288), (59095, 2651), (63184, 669),
  (69277, 2336), (69855, 1657), (76868, 2672), (84359, 235), (106379, 1205),
  (107710, 2368)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X5Y0_check. -/
theorem X1Split76A0X5Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X5Y0_pairs. -/
theorem X1Split76A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk5 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X5_pairs. -/
theorem X1Split76A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X6Y0Certs : List (Nat × Nat) := [
  (13717, 2870), (19304, 1018), (25070, 2619), (31277, 3360), (34054, 3429),
  (46570, 3522), (46997, 765), (47052, 2643), (47116, 3270), (47342, 881),
  (47397, 795), (57763, 1510), (64827, 3185), (64973, 790), (74421, 340),
  (74460, 2614), (76013, 2833), (86976, 1453), (99344, 338)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X6Y0_check. -/
theorem X1Split76A0X6Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X6Y0_pairs. -/
theorem X1Split76A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk6 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X6_pairs. -/
theorem X1Split76A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X7Y0Certs : List (Nat × Nat) := [
  (992, 955), (996, 1664), (25263, 626), (28843, 1055), (30839, 3025),
  (42381, 1993), (48557, 1019), (48655, 3325), (50026, 342), (50042, 1706),
  (50093, 2613), (50180, 3206), (50458, 882), (52329, 690), (60471, 749),
  (62641, 2966), (63002, 3037), (63008, 3152), (63014, 3521), (63073, 2979),
  (63964, 124), (67967, 1336), (67977, 2755), (69779, 1280), (85404, 336),
  (85619, 2644), (87905, 392), (94277, 2909), (94336, 3155), (101453, 1601)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X7Y0_check. -/
theorem X1Split76A0X7Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X7Y0_pairs. -/
theorem X1Split76A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X7Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk7 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X7_pairs. -/
theorem X1Split76A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X8Y0Certs : List (Nat × Nat) := [
  (6668, 1505), (8757, 652), (9250, 1236), (16317, 3348), (17717, 2115),
  (17831, 2834), (25518, 907), (38301, 1973), (60910, 322), (61058, 3195),
  (65743, 1883), (93961, 3193), (94102, 122), (94115, 321), (94334, 759),
  (94393, 3297)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X8Y0_check. -/
theorem X1Split76A0X8Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X8Y0_pairs. -/
theorem X1Split76A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X8Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk8 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X8_pairs. -/
theorem X1Split76A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X9Y0Certs : List (Nat × Nat) := [
  (2796, 1340), (3690, 1343), (3696, 1750), (4605, 1745), (11073, 511),
  (12403, 1269), (14694, 2207), (18920, 1652), (20136, 1820), (32994, 1342),
  (41564, 2403), (45781, 2446), (50333, 3069), (53392, 2849), (60684, 1271),
  (84585, 1009), (84910, 1531), (95739, 1950), (96382, 1885), (104215, 3528)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X9Y0_check. -/
theorem X1Split76A0X9Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X9Y0_pairs. -/
theorem X1Split76A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X9Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk9 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X9_pairs. -/
theorem X1Split76A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X10Y0Certs : List (Nat × Nat) := [
  (9288, 1146), (9300, 2745), (9399, 1740), (9405, 2742), (9492, 2748),
  (9632, 3199), (9830, 1599), (15717, 2424), (44677, 2201), (56879, 196),
  (64395, 770), (64397, 412), (64645, 391), (64797, 341), (64813, 1638),
  (67126, 1891), (76067, 3253), (81394, 272), (85893, 2429), (87468, 347),
  (90285, 3079), (100157, 815), (100218, 3248), (100621, 812), (102272, 978),
  (107967, 602), (108387, 1650), (108462, 1717), (108480, 3312), (108570, 1653),
  (108738, 808)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X10Y0_check. -/
theorem X1Split76A0X10Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X10Y0_pairs. -/
theorem X1Split76A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X10Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk10 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X10_pairs. -/
theorem X1Split76A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X11Y0Certs : List (Nat × Nat) := [
  (12625, 2325), (16500, 3525), (22665, 1707), (22671, 349), (40955, 2420),
  (53049, 335), (81383, 1608), (82047, 810), (82200, 3313), (84192, 1756),
  (84198, 2763)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X11Y0_check. -/
theorem X1Split76A0X11Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X11Y0_pairs. -/
theorem X1Split76A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X11Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk11 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X11_pairs. -/
theorem X1Split76A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X12Y0Certs : List (Nat × Nat) := [
  (2627, 1637), (3027, 1604), (3033, 2611), (3039, 3204), (3043, 411),
  (10979, 914), (12281, 1381), (14134, 1092), (17215, 1961), (19719, 2385),
  (27480, 393), (29702, 2668), (29712, 827), (35967, 2389), (44745, 1893),
  (44800, 1897), (46995, 601), (46997, 818), (47052, 2661), (47139, 3246),
  (47397, 814), (50706, 1512), (61551, 1581), (61563, 3292), (63365, 532),
  (83051, 766), (83084, 3300), (104230, 2915), (109482, 1739), (109621, 2114),
  (109773, 3427), (109988, 2832), (109994, 3423), (110038, 3430), (110927, 738),
  (110992, 2636)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X12Y0_check. -/
theorem X1Split76A0X12Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X12Y0_pairs. -/
theorem X1Split76A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X12Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk12 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X12_pairs. -/
theorem X1Split76A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X13Y0Certs : List (Nat × Nat) := [
  (1227, 2838), (7544, 480), (7759, 2650), (11246, 2746), (19019, 1163),
  (21052, 456), (24990, 3136), (31907, 2019), (32236, 2747), (34173, 688),
  (53911, 254), (60577, 571), (63904, 1449), (66459, 1836), (69512, 1548),
  (72505, 2985), (72859, 1794), (77822, 2298), (83489, 3413), (93196, 476),
  (109327, 2055)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X13Y0_check. -/
theorem X1Split76A0X13Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X13Y0_pairs. -/
theorem X1Split76A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X13Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk13 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X13_pairs. -/
theorem X1Split76A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X14Y0Certs : List (Nat × Nat) := [
  (2920, 1868), (3229, 2549), (15574, 337), (30957, 2724), (31032, 2657),
  (31149, 3244), (31247, 544), (31302, 952), (31488, 916), (50697, 3353),
  (50709, 1765), (52737, 809), (64098, 327), (64100, 786), (64104, 1698),
  (64110, 2585), (64215, 2601), (98310, 320), (98377, 2604), (99243, 541),
  (99539, 1654), (105816, 2664), (106776, 1147), (106946, 1742), (110392, 2841),
  (110398, 3432)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X14Y0_check. -/
theorem X1Split76A0X14Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X14Y0_pairs. -/
theorem X1Split76A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X14Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk14 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X14_pairs. -/
theorem X1Split76A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X15Y0Certs : List (Nat × Nat) := [
  (21073, 1202), (24371, 1795), (39589, 158), (41099, 1319), (43271, 2040),
  (45277, 1812), (48634, 54), (52467, 1651), (60523, 745), (60874, 1700),
  (74451, 1292), (74453, 1339), (74457, 1753), (74532, 1749), (74550, 3341),
  (79081, 2397)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X15Y0_check. -/
theorem X1Split76A0X15Y0_check : checkGrid m4TX1 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X15Y0_pairs. -/
theorem X1Split76A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X15Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk15 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X15_pairs. -/
theorem X1Split76A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0_pairs. -/
theorem X1Split76A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split76A0X0_pairs x hx y hy hw
  · exact X1Split76A0X1_pairs x hx y hy hw
  · exact X1Split76A0X2_pairs x hx y hy hw
  · exact X1Split76A0X3_pairs x hx y hy hw
  · exact X1Split76A0X4_pairs x hx y hy hw
  · exact X1Split76A0X5_pairs x hx y hy hw
  · exact X1Split76A0X6_pairs x hx y hy hw
  · exact X1Split76A0X7_pairs x hx y hy hw
  · exact X1Split76A0X8_pairs x hx y hy hw
  · exact X1Split76A0X9_pairs x hx y hy hw
  · exact X1Split76A0X10_pairs x hx y hy hw
  · exact X1Split76A0X11_pairs x hx y hy hw
  · exact X1Split76A0X12_pairs x hx y hy hw
  · exact X1Split76A0X13_pairs x hx y hy hw
  · exact X1Split76A0X14_pairs x hx y hy hw
  · exact X1Split76A0X15_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split76_check. -/
theorem X1Split76_check : checkSplit m4TX1 (3, 2, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X0Y0Certs : List (Nat × Nat) := [
  (27584, 989), (27733, 2273), (28862, 820), (42245, 262), (52788, 840),
  (57635, 1264), (58978, 1575), (59137, 3186), (73595, 429), (77138, 761),
  (77408, 3196), (79366, 1123), (79378, 1219), (80145, 567), (80952, 222),
  (89018, 1782), (91623, 1737)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X0Y0_check. -/
theorem X1Split77A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X0Y0_pairs. -/
theorem X1Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X0_pairs. -/
theorem X1Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X1Y0Certs : List (Nat × Nat) := [
  (12707, 492), (33282, 1295), (33432, 2751), (50320, 1901), (50351, 2269),
  (59827, 1403), (59876, 1791), (61184, 1804), (61247, 2452), (63367, 1862),
  (64406, 155), (64670, 1840), (67700, 1755), (81188, 1781), (84518, 662),
  (99226, 253), (109315, 673)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X1Y0_check. -/
theorem X1Split77A0X1Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X1Y0_pairs. -/
theorem X1Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X1_pairs. -/
theorem X1Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X2Y0Certs : List (Nat × Nat) := [
  (15619, 2959), (16335, 1429), (23356, 2039), (24004, 428), (28276, 36),
  (36495, 2912), (36510, 3149), (43111, 252), (46887, 2381), (50537, 399),
  (50813, 2587), (53076, 69), (54577, 1150), (70416, 2867), (74432, 255),
  (74548, 870), (83901, 2869), (84132, 983), (95354, 472), (95531, 1644),
  (100467, 3212), (103232, 737), (104700, 2036), (104712, 2079), (105917, 1254),
  (107997, 603), (109298, 584)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X2Y0_check. -/
theorem X1Split77A0X2Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X2Y0_pairs. -/
theorem X1Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk2 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X2_pairs. -/
theorem X1Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X3Y0Certs : List (Nat × Nat) := [
  (9105, 3150), (10458, 119), (15166, 2829), (25395, 884), (26270, 926),
  (26453, 2588), (36276, 967), (83946, 3332), (84965, 748), (85180, 2596),
  (87194, 1118)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X3Y0_check. -/
theorem X1Split77A0X3Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X3Y0_pairs. -/
theorem X1Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk3 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X3_pairs. -/
theorem X1Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X4Y0Certs : List (Nat × Nat) := [
  (2815, 1183), (30169, 846), (30422, 3173), (44924, 614), (55152, 2382),
  (56139, 144), (64718, 2322), (66795, 1427), (67874, 96), (68139, 1784),
  (69809, 1224), (91833, 257), (92114, 2276), (94054, 497), (94290, 2279),
  (98109, 1407), (99895, 1788), (100138, 464), (100243, 1114), (105647, 2839)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X4Y0_check. -/
theorem X1Split77A0X4Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X4Y0_pairs. -/
theorem X1Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk4 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X4_pairs. -/
theorem X1Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X5Y0Certs : List (Nat × Nat) := [
  (14373, 120), (19820, 1455), (33171, 578), (33328, 1656), (34549, 1027),
  (34617, 1546), (35851, 1006), (41200, 2071), (41977, 1267), (63199, 648),
  (69708, 570), (79852, 1476), (106379, 1423), (107785, 2358)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X5Y0_check. -/
theorem X1Split77A0X5Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X5Y0_pairs. -/
theorem X1Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk5 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X5_pairs. -/
theorem X1Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X6Y0Certs : List (Nat × Nat) := [
  (13867, 2875), (19315, 974), (33077, 117), (34352, 3250), (47141, 867),
  (47394, 3203), (59284, 651), (65073, 1588), (71075, 925), (71317, 3188),
  (74423, 212), (76008, 2120), (76907, 2455), (79900, 1904), (99215, 191)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X6Y0_check. -/
theorem X1Split77A0X6Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X6Y0_pairs. -/
theorem X1Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk6 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X6_pairs. -/
theorem X1Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X7Y0Certs : List (Nat × Nat) := [
  (990, 642), (996, 655), (17896, 323), (18106, 1693), (27875, 190),
  (28998, 1829), (30761, 2075), (48473, 1083), (48655, 2736), (50287, 1606),
  (50440, 3205), (55827, 773), (59104, 2863), (60722, 1585), (63020, 2865),
  (63036, 2970), (63961, 114), (68088, 1341), (69824, 1305), (85674, 3202),
  (87943, 384), (91659, 2066), (94394, 3518)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X7Y0_check. -/
theorem X1Split77A0X7Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X7Y0_pairs. -/
theorem X1Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X7Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk7 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X7_pairs. -/
theorem X1Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X8Y0Certs : List (Nat × Nat) := [
  (8824, 649), (9365, 1363), (15114, 2229), (16316, 1291), (17723, 2220),
  (54261, 2161), (60910, 90), (60971, 374), (93966, 70), (94019, 319)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X8Y0_check. -/
theorem X1Split77A0X8Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X8Y0_pairs. -/
theorem X1Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X8Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk8 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X8_pairs. -/
theorem X1Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X9Y0Certs : List (Nat × Nat) := [
  (3702, 1294), (4559, 1225), (10910, 189), (12403, 1299), (14694, 2347),
  (18963, 1587), (20965, 444), (32840, 1263), (41936, 976), (46015, 2360),
  (47874, 145), (47904, 286), (50349, 2231), (84866, 220), (84952, 657),
  (87485, 263), (87632, 1126), (93213, 647), (93857, 2291), (95739, 213),
  (96322, 1064), (96442, 2057), (104376, 3183)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X9Y0_check. -/
theorem X1Split77A0X9Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X9Y0_pairs. -/
theorem X1Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X9Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk9 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X9_pairs. -/
theorem X1Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X10Y0Certs : List (Nat × Nat) := [
  (9327, 1113), (9342, 1214), (9643, 385), (16005, 2423), (22090, 2359),
  (44757, 2898), (46187, 400), (46363, 1576), (56594, 231), (64418, 210),
  (64525, 768), (67275, 1811), (89247, 377), (90287, 1438), (100161, 577),
  (100589, 548), (108406, 491), (108417, 539)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X10Y0_check. -/
theorem X1Split77A0X10Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X10Y0_pairs. -/
theorem X1Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X10Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk10 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X10_pairs. -/
theorem X1Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X11Y0Certs : List (Nat × Nat) := [
  (14595, 1426), (16473, 2861), (22981, 2617), (28170, 2282), (32469, 1787),
  (52665, 174), (56582, 178), (81705, 2612), (81882, 537), (84188, 1404),
  (84198, 1441)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X11Y0_check. -/
theorem X1Split77A0X11Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X11Y0_pairs. -/
theorem X1Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X11Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk11 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X11_pairs. -/
theorem X1Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X12Y0Certs : List (Nat × Nat) := [
  (1018, 783), (1221, 2581), (2638, 172), (2644, 186), (11041, 903),
  (16199, 547), (17121, 853), (19970, 2964), (27475, 373), (30002, 3251),
  (44669, 2016), (44800, 3412), (47096, 599), (47346, 2660), (54645, 1667),
  (60961, 324), (61251, 2582), (61335, 22), (63266, 1111), (78693, 2942),
  (82713, 334), (101602, 1477), (101752, 2981), (104353, 2902), (109926, 2053),
  (109943, 2219), (111079, 844)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X12Y0_check. -/
theorem X1Split77A0X12Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X12Y0_pairs. -/
theorem X1Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X12Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk12 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X12_pairs. -/
theorem X1Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X13Y0Certs : List (Nat × Nat) := [
  (1194, 2228), (7561, 902), (11240, 2656), (17638, 1416), (18809, 546),
  (21052, 969), (23573, 439), (24990, 1120), (32551, 2616), (35419, 1026),
  (53551, 250), (60577, 580), (66841, 1816), (69463, 1972), (69556, 2917),
  (72436, 1325), (72554, 2396), (72860, 1266), (75340, 446), (75390, 714),
  (77811, 2866), (109490, 2051)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X13Y0_check. -/
theorem X1Split77A0X13Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X13Y0_pairs. -/
theorem X1Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X13Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk13 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X13_pairs. -/
theorem X1Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X14Y0Certs : List (Nat × Nat) := [
  (3160, 597), (3289, 1446), (5785, 674), (5968, 2084), (15290, 343),
  (30978, 496), (30988, 542), (31482, 869), (39368, 1272), (50702, 1439),
  (52732, 504), (56113, 3442), (64001, 310), (64199, 1577), (65350, 520),
  (91063, 784), (91323, 3176), (98318, 74), (99330, 807), (106126, 3245),
  (106782, 1215), (110386, 2287), (110398, 2388)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X14Y0_check. -/
theorem X1Split77A0X14Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X14Y0_pairs. -/
theorem X1Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X14Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk14 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X14_pairs. -/
theorem X1Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X15Y0Certs : List (Nat × Nat) := [
  (21184, 2046), (37681, 1694), (37818, 3175), (41061, 968), (47624, 1226),
  (48306, 139), (52461, 1603), (60523, 317), (60819, 2593), (74612, 1335),
  (74812, 3339), (82589, 2767)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X15Y0_check. -/
theorem X1Split77A0X15Y0_check : checkGrid m4TX1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X15Y0_pairs. -/
theorem X1Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X15Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk15 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X15_pairs. -/
theorem X1Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0_pairs. -/
theorem X1Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split77A0X0_pairs x hx y hy hw
  · exact X1Split77A0X1_pairs x hx y hy hw
  · exact X1Split77A0X2_pairs x hx y hy hw
  · exact X1Split77A0X3_pairs x hx y hy hw
  · exact X1Split77A0X4_pairs x hx y hy hw
  · exact X1Split77A0X5_pairs x hx y hy hw
  · exact X1Split77A0X6_pairs x hx y hy hw
  · exact X1Split77A0X7_pairs x hx y hy hw
  · exact X1Split77A0X8_pairs x hx y hy hw
  · exact X1Split77A0X9_pairs x hx y hy hw
  · exact X1Split77A0X10_pairs x hx y hy hw
  · exact X1Split77A0X11_pairs x hx y hy hw
  · exact X1Split77A0X12_pairs x hx y hy hw
  · exact X1Split77A0X13_pairs x hx y hy hw
  · exact X1Split77A0X14_pairs x hx y hy hw
  · exact X1Split77A0X15_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split77_check. -/
theorem X1Split77_check : checkSplit m4TX1 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split78A0X0Y0Certs : List (Nat × Nat) := [
  (3647, 727), (3659, 3164), (4062, 354), (9981, 1241), (14611, 20),
  (16951, 13), (16975, 2028), (17321, 302), (17333, 1570), (17406, 106),
  (17878, 2852), (18858, 830), (22262, 23), (22278, 828), (22898, 161),
  (22905, 564), (24791, 295), (24807, 2570), (24846, 108), (30821, 293),
  (32791, 14), (33824, 481), (33825, 565), (37389, 203), (40695, 566),
  (42904, 60), (45868, 2856), (46500, 1), (47014, 62), (47038, 2854),
  (48377, 731), (48387, 2580), (48492, 360), (49328, 167), (50970, 4),
  (55017, 2579), (55583, 1565), (57600, 2), (57606, 101), (58574, 483),
  (58581, 1249), (62090, 1099), (62091, 1245), (65027, 724), (67924, 63),
  (70340, 1106), (71768, 163), (75435, 560), (77450, 1107), (79412, 27),
  (79869, 202), (79888, 2855), (79982, 29), (80708, 168), (80709, 205),
  (81249, 206), (82973, 1568), (82979, 3162), (83088, 834), (84284, 490),
  (92249, 3163), (93117, 2572), (95912, 26), (95922, 358), (96377, 726),
  (96511, 15), (96530, 1103), (99411, 1247), (99745, 2034), (101875, 2027),
  (104114, 485), (111360, 0), (111372, 359), (113813, 1569), (116644, 59),
  (116665, 2032), (117791, 300), (118319, 3161), (120876, 105), (120888, 837)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X0Y0_check. -/
theorem X1Split78A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X0Y0_pairs. -/
theorem X1Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks3S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split78A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X0_pairs. -/
theorem X1Split78A0X0_pairs : ∀ x ∈ outerMasks3S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0_pairs. -/
theorem X1Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split78A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split78_check. -/
theorem X1Split78_check : checkSplit m4TX1 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X0Y0_check. -/
theorem X1Split79A0X0Y0_check : checkGrid m4TX1 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X0Y0_pairs. -/
theorem X1Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split79A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X0_pairs. -/
theorem X1Split79A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0_pairs. -/
theorem X1Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split79A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split79_check. -/
theorem X1Split79_check : checkSplit m4TX1 (3, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split79A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X0Y0Certs : List (Nat × Nat) := [
  (1428, 2921), (3341, 3426), (3806, 2969), (5337, 1850), (6389, 995),
  (9612, 2914), (9672, 1691), (13043, 1330), (13834, 2433), (14089, 1238),
  (17571, 2818), (19491, 895), (21710, 1463), (21842, 2250), (22003, 3131),
  (22894, 2203), (23988, 3490), (24492, 2054), (26733, 1364), (26929, 917)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X0Y0_check. -/
theorem X1Split80A0X0Y0_check : checkGrid m4TX1 1 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X0Y0_pairs. -/
theorem X1Split80A0X0Y0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S32768Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X0_pairs. -/
theorem X1Split80A0X0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0_pairs. -/
theorem X1Split80A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split80A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split80_check. -/
theorem X1Split80_check : checkSplit m4TX1 (4, 0, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split80A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X0Y0Certs : List (Nat × Nat) := [
  (5673, 1834), (44213, 2018), (53077, 1001), (56433, 2936), (80315, 1365),
  (81229, 2471), (118716, 2913), (118938, 1833)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X0Y0_check. -/
theorem X1Split81A0X0Y0_check : checkGrid m4TX1 1 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X0Y0_pairs. -/
theorem X1Split81A0X0Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S4096Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X0_pairs. -/
theorem X1Split81A0X0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X1Y0Certs : List (Nat × Nat) := [
  (7716, 477), (18880, 552), (34265, 2378), (37083, 526), (39442, 2243),
  (54798, 522), (66422, 1803), (72897, 2609), (74477, 3042), (88139, 3240),
  (91856, 516), (94303, 1856), (108307, 1189), (108893, 2754)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X1Y0_check. -/
theorem X1Split81A0X1Y0_check : checkGrid m4TX1 1 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X1Y0_pairs. -/
theorem X1Split81A0X1Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S4096Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S4096Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S4096Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X1_pairs. -/
theorem X1Split81A0X1_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X2Y0Certs : List (Nat × Nat) := [
  (8909, 2377), (50440, 2067), (52434, 2439), (75827, 1927), (85306, 1233),
  (86562, 868), (87420, 972), (102311, 1040), (115392, 1093)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X2Y0_check. -/
theorem X1Split81A0X2Y0_check : checkGrid m4TX1 1 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X2Y0_pairs. -/
theorem X1Split81A0X2Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S4096Chunk2_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S4096Chunk2 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk2_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S4096Chunk2_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X2_pairs. -/
theorem X1Split81A0X2_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X3Y0Certs : List (Nat × Nat) := [
  (22895, 1171), (44689, 2997), (46566, 2289), (47920, 1530), (51739, 3006),
  (52096, 3081), (53767, 1192), (53959, 1300), (57896, 3047), (58319, 1148),
  (58673, 2671), (78090, 1184), (85573, 1483), (116773, 2180), (116942, 2456),
  (117807, 3242), (121646, 617)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X3Y0_check. -/
theorem X1Split81A0X3Y0_check : checkGrid m4TX1 1 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X3Y0_pairs. -/
theorem X1Split81A0X3Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S4096Chunk3_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S4096Chunk3 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk3_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S4096Chunk3_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X3_pairs. -/
theorem X1Split81A0X3_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X4Y0Certs : List (Nat × Nat) := [
  (6150, 1478), (29021, 1506), (99586, 2947), (102483, 266)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X4Y0_check. -/
theorem X1Split81A0X4Y0_check : checkGrid m4TX1 1 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X4Y0_pairs. -/
theorem X1Split81A0X4Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S4096Chunk4_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S4096Chunk4 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk4_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S4096Chunk4_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X4_pairs. -/
theorem X1Split81A0X4_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X5Y0Certs : List (Nat × Nat) := [
  (8552, 2168), (11904, 180), (16282, 3008), (37243, 2183), (37330, 2146),
  (37817, 2502), (39984, 986), (42746, 1435), (49908, 923), (61944, 2061),
  (72262, 2960), (72762, 397), (74836, 2548), (80555, 193), (81311, 2117),
  (81897, 3359)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X5Y0_check. -/
theorem X1Split81A0X5Y0_check : checkGrid m4TX1 1 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X5Y0_pairs. -/
theorem X1Split81A0X5Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S4096Chunk5_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S4096Chunk5 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk5_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S4096Chunk5_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X5_pairs. -/
theorem X1Split81A0X5_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X6Y0Certs : List (Nat × Nat) := [
  (21577, 677), (24712, 1286)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X6Y0_check. -/
theorem X1Split81A0X6Y0_check : checkGrid m4TX1 1 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X6Y0_pairs. -/
theorem X1Split81A0X6Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 1 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S4096Chunk6_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S4096Chunk6 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S4096Chunk6_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks4S4096Chunk6_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X6_pairs. -/
theorem X1Split81A0X6_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0_pairs. -/
theorem X1Split81A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split81A0X0_pairs x hx y hy hw
  · exact X1Split81A0X1_pairs x hx y hy hw
  · exact X1Split81A0X2_pairs x hx y hy hw
  · exact X1Split81A0X3_pairs x hx y hy hw
  · exact X1Split81A0X4_pairs x hx y hy hw
  · exact X1Split81A0X5_pairs x hx y hy hw
  · exact X1Split81A0X6_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split81_check. -/
theorem X1Split81_check : checkSplit m4TX1 (4, 1, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split81A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A0X0Y0Certs : List (Nat × Nat) := [
  (454, 0), (475, 215), (2102, 0), (2533, 0), (2990, 0),
  (3548, 366), (4068, 0), (5086, 0), (5232, 0), (5414, 0),
  (7509, 591), (8323, 316), (9173, 209), (10877, 38), (14003, 437),
  (15365, 747), (15924, 1614), (17217, 1545), (17411, 0), (18429, 857),
  (18530, 1598), (18588, 0), (19622, 0), (20103, 495), (20715, 0),
  (22350, 0), (24274, 2511), (26997, 0), (27277, 2056), (27669, 1615),
  (28710, 0), (32768, 760), (34911, 576), (35359, 0), (36439, 0),
  (37492, 431), (37864, 121), (38149, 0), (38770, 0), (40143, 645),
  (43681, 1005), (44079, 764), (44106, 0), (45502, 1605), (46110, 0),
  (46186, 395), (46321, 1251), (47742, 2270), (48233, 2879), (49046, 2268),
  (49078, 0), (49106, 0), (51259, 2649), (54136, 1122), (55826, 0),
  (58524, 0), (59304, 0), (60043, 93), (62094, 0), (62983, 2387),
  (64155, 0), (64895, 0), (65206, 2918), (65262, 92), (65618, 2677),
  (66443, 2218), (66563, 0), (66867, 0), (67222, 0), (67463, 0),
  (67866, 67), (68370, 0), (68416, 0), (68613, 0), (68718, 3259),
  (68750, 0), (68771, 219), (69272, 0), (71965, 0), (71986, 1252),
  (74874, 285), (77217, 1293), (78771, 0), (80655, 997), (80985, 390),
  (82504, 0), (84628, 1414), (85222, 2982), (85716, 0), (86334, 1167),
  (87450, 111), (87735, 0), (89467, 1863), (89877, 1648), (91281, 2659),
  (92775, 0), (92780, 0), (93097, 72), (93106, 0), (93259, 919),
  (95116, 1815), (95285, 125), (95490, 1317), (95570, 0), (96798, 0),
  (97019, 95), (98501, 0), (99605, 3322), (102476, 1527), (103327, 1402),
  (104162, 1125)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X0Y0_check. -/
theorem X1Split82A0X0Y0_check : checkGrid m4TX1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X0Y0_pairs. -/
theorem X1Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X0_pairs. -/
theorem X1Split82A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A0X1Y0Certs : List (Nat × Nat) := [
  (1357, 273), (4795, 89), (5899, 0), (6286, 0), (6410, 2140),
  (7139, 990), (7329, 0), (7337, 0), (7446, 269), (7563, 0),
  (7705, 0), (7824, 3368), (8670, 3148), (10575, 713), (12206, 0),
  (14074, 845), (15310, 0), (16636, 0), (16735, 0), (17691, 1853),
  (18003, 912), (21663, 0), (22268, 0), (22978, 2605), (23006, 2892),
  (23094, 0), (23393, 2323), (23774, 1805), (24885, 0), (25440, 0),
  (25523, 1887), (25550, 2141), (26603, 367), (28509, 1408), (29081, 2741),
  (29273, 0), (29931, 0), (32584, 0), (34280, 2543), (35564, 2277),
  (36418, 2085), (36835, 0), (36936, 2971), (38902, 0), (43090, 0),
  (43372, 0), (44871, 364), (46678, 692), (47245, 0), (47490, 0),
  (48030, 0), (50072, 256), (50482, 0), (51400, 0), (51632, 0),
  (51733, 3073), (52332, 686), (52562, 2623), (53837, 2292), (53857, 0),
  (54431, 309), (56137, 143), (58098, 1442), (58233, 0), (59579, 3235),
  (59771, 977), (60124, 498), (60556, 0), (61789, 0), (62026, 1582),
  (62173, 3074), (62763, 0), (63001, 0), (63463, 0), (64145, 0),
  (64811, 3421), (65050, 0), (66748, 1115), (67527, 538), (70549, 0),
  (70793, 0), (70851, 0), (71495, 850), (71507, 0), (73575, 0),
  (73692, 0), (75289, 0), (75645, 0), (75871, 0), (76251, 656),
  (76441, 0), (77152, 0), (77381, 2893), (77679, 1508)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X1Y0_check. -/
theorem X1Split82A0X1Y0_check : checkGrid m4TX1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X1Y0_pairs. -/
theorem X1Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X1_pairs. -/
theorem X1Split82A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0_pairs. -/
theorem X1Split82A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split82A0X0_pairs x hx y hy hw
  · exact X1Split82A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A1X0Y0Certs : List (Nat × Nat) := [
  (3619, 744), (14744, 2908), (14773, 0), (19690, 596), (28482, 1213),
  (47529, 592), (52769, 701), (71942, 0), (73197, 0), (86312, 1015),
  (104712, 2080), (104782, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X0Y0_check. -/
theorem X1Split82A1X0Y0_check : checkGrid m4TX1 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X0Y0_pairs. -/
theorem X1Split82A1X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X0_pairs. -/
theorem X1Split82A1X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A1X1Y0Certs : List (Nat × Nat) := [
  (20658, 1258), (23734, 0), (33626, 0), (38109, 0), (52762, 0),
  (53049, 3201), (56895, 0), (59259, 514), (63234, 859), (65211, 0),
  (71508, 0), (73330, 1516), (77505, 0), (77853, 3262)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X1Y0_check. -/
theorem X1Split82A1X1Y0_check : checkGrid m4TX1 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X1Y0_pairs. -/
theorem X1Split82A1X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X1_pairs. -/
theorem X1Split82A1X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1_pairs. -/
theorem X1Split82A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split82A1X0_pairs x hx y hy hw
  · exact X1Split82A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A2X0Y0Certs : List (Nat × Nat) := [
  (15, 110), (287, 1826), (300, 0), (1300, 3411), (1950, 1250),
  (3547, 0), (16135, 216), (16326, 1400), (20102, 0), (24967, 0),
  (29347, 0), (29507, 2621), (31545, 1316), (36509, 0), (46913, 2676),
  (47741, 0), (50961, 362), (52930, 0), (53296, 1324), (64149, 1166),
  (65261, 0), (66562, 71), (70770, 0), (71987, 0), (73346, 1643),
  (88836, 0), (91720, 2735), (93392, 0), (93553, 171), (94389, 3367),
  (95753, 279), (98225, 0), (99335, 848), (103328, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X0Y0_check. -/
theorem X1Split82A2X0Y0_check : checkGrid m4TX1 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X0Y0_pairs. -/
theorem X1Split82A2X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X0_pairs. -/
theorem X1Split82A2X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A2X1Y0Certs : List (Nat × Nat) := [
  (3577, 0), (7486, 0), (18209, 0), (20714, 0), (25422, 0),
  (30007, 3338), (31649, 0), (52055, 1841), (54432, 0), (70134, 515)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X1Y0_check. -/
theorem X1Split82A2X1Y0_check : checkGrid m4TX1 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X1Y0_pairs. -/
theorem X1Split82A2X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X1_pairs. -/
theorem X1Split82A2X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2_pairs. -/
theorem X1Split82A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split82A2X0_pairs x hx y hy hw
  · exact X1Split82A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A3X0Y0Certs : List (Nat × Nat) := [
  (27730, 2267)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X0Y0_check. -/
theorem X1Split82A3X0Y0_check : checkGrid m4TX1 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X0Y0_pairs. -/
theorem X1Split82A3X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X0_pairs. -/
theorem X1Split82A3X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A3X1Y0Certs : List (Nat × Nat) := [
  (30219, 0), (58022, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X1Y0_check. -/
theorem X1Split82A3X1Y0_check : checkGrid m4TX1 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X1Y0_pairs. -/
theorem X1Split82A3X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split82A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X1_pairs. -/
theorem X1Split82A3X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split82A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3_pairs. -/
theorem X1Split82A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split82A3X0_pairs x hx y hy hw
  · exact X1Split82A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split82_check. -/
theorem X1Split82_check : checkSplit m4TX1 (4, 2, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split82A0_pairs x hx y hy hw
    · exact X1Split82A1_pairs x hx y hy hw
    · exact X1Split82A2_pairs x hx y hy hw
    · exact X1Split82A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X0Y0Certs : List (Nat × Nat) := [
  (29936, 2259), (63050, 1104), (68422, 1396), (79375, 2026), (79741, 17),
  (97370, 1108), (113189, 3167)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X0Y0_check. -/
theorem X1Split83A0X0Y0_check : checkGrid m4TX1 0 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X0Y0_pairs. -/
theorem X1Split83A0X0Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks4S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S4096Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X0_pairs. -/
theorem X1Split83A0X0_pairs : ∀ x ∈ outerMasks4S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X1Y0Certs : List (Nat × Nat) := [
  (18310, 241), (22355, 80), (27990, 5), (38904, 1768), (56283, 49),
  (68929, 956), (79576, 631), (94270, 242), (99079, 960)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X1Y0_check. -/
theorem X1Split83A0X1Y0_check : checkGrid m4TX1 0 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X1Y0_pairs. -/
theorem X1Split83A0X1Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks4S4096Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X1Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S4096Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S4096Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S4096Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X1_pairs. -/
theorem X1Split83A0X1_pairs : ∀ x ∈ outerMasks4S4096Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X2Y0Certs : List (Nat × Nat) := [
  (2635, 2035), (14426, 2264), (31901, 296), (45889, 959), (48058, 2851),
  (48664, 57), (50362, 1391), (51271, 12), (77716, 633)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X2Y0_check. -/
theorem X1Split83A0X2Y0_check : checkGrid m4TX1 0 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X2Y0_pairs. -/
theorem X1Split83A0X2Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks4S4096Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk2 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X2Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S4096Chunk2_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S4096Chunk2 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk2_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S4096Chunk2_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X2_pairs. -/
theorem X1Split83A0X2_pairs : ∀ x ∈ outerMasks4S4096Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X3Y0Certs : List (Nat × Nat) := [
  (8410, 244), (14366, 2263), (33512, 30), (33769, 958), (53536, 634),
  (56583, 41), (72937, 129), (90455, 86), (93504, 1773), (95380, 239),
  (102403, 422), (115933, 415)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X3Y0_check. -/
theorem X1Split83A0X3Y0_check : checkGrid m4TX1 0 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X3Y0_pairs. -/
theorem X1Split83A0X3Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks4S4096Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk3 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X3Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S4096Chunk3_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S4096Chunk3 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk3_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S4096Chunk3_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X3_pairs. -/
theorem X1Split83A0X3_pairs : ∀ x ∈ outerMasks4S4096Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X4Y0Certs : List (Nat × Nat) := [
  (5017, 135), (14728, 2853), (35318, 170), (40635, 557), (53154, 1772),
  (72407, 728), (75732, 351), (81638, 164), (90459, 198), (95866, 636),
  (99446, 2260), (99543, 48), (100804, 61)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X4Y0_check. -/
theorem X1Split83A0X4Y0_check : checkGrid m4TX1 0 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X4Y0_pairs. -/
theorem X1Split83A0X4Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks4S4096Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk4 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X4Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S4096Chunk4_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S4096Chunk4 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk4_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S4096Chunk4_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X4_pairs. -/
theorem X1Split83A0X4_pairs : ∀ x ∈ outerMasks4S4096Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X5Y0Certs : List (Nat × Nat) := [
  (8157, 2574), (14473, 424), (16505, 85), (16813, 416), (34282, 1395),
  (58026, 103), (58434, 1771), (69967, 136), (99742, 1390), (102254, 484),
  (109128, 831), (121071, 1240)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X5Y0_check. -/
theorem X1Split83A0X5Y0_check : checkGrid m4TX1 0 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X5Y0_pairs. -/
theorem X1Split83A0X5Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks4S4096Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk5 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X5Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S4096Chunk5_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S4096Chunk5 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk5_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S4096Chunk5_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X5_pairs. -/
theorem X1Split83A0X5_pairs : ∀ x ∈ outerMasks4S4096Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X6Y0Certs : List (Nat × Nat) := [
  (22625, 82), (24277, 128), (25113, 47), (28479, 204), (37821, 1242),
  (50753, 1567), (55304, 487), (68205, 559)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X6Y0_check. -/
theorem X1Split83A0X6Y0_check : checkGrid m4TX1 0 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X6Y0_pairs. -/
theorem X1Split83A0X6Y0_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 3
    outerMasks4S4096Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S4096Chunk6 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X6Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S4096Chunk6_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S4096Chunk6 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S4096Chunk6_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S4096Chunk6_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X6_pairs. -/
theorem X1Split83A0X6_pairs : ∀ x ∈ outerMasks4S4096Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0_pairs. -/
theorem X1Split83A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split83A0X0_pairs x hx y hy hw
  · exact X1Split83A0X1_pairs x hx y hy hw
  · exact X1Split83A0X2_pairs x hx y hy hw
  · exact X1Split83A0X3_pairs x hx y hy hw
  · exact X1Split83A0X4_pairs x hx y hy hw
  · exact X1Split83A0X5_pairs x hx y hy hw
  · exact X1Split83A0X6_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split83_check. -/
theorem X1Split83_check : checkSplit m4TX1 (4, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split83A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X0Y0_check. -/
theorem X1Split84A0X0Y0_check : checkGrid m4TX1 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X0Y0_pairs. -/
theorem X1Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 0 0 4
    outerMasks4S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S32768Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks4S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X0_pairs. -/
theorem X1Split84A0X0_pairs : ∀ x ∈ outerMasks4S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0_pairs. -/
theorem X1Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split84A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split84_check. -/
theorem X1Split84_check : checkSplit m4TX1 (4, 4, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 4 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split84A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A0X0Y0Certs : List (Nat × Nat) := [
  (277, 0), (541, 0), (1822, 0), (2044, 0), (2412, 0),
  (3416, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0Y0_check. -/
theorem X1Split85A0X0Y0_check : checkGrid m4TX1 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0Y0_pairs. -/
theorem X1Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X1Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0_pairs. -/
theorem X1Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split85A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0_pairs. -/
theorem X1Split85A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split85A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A1X0Y0Certs : List (Nat × Nat) := [
  (3773, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0Y0_check. -/
theorem X1Split85A1X0Y0_check : checkGrid m4TX1 2 91076351 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0Y0_pairs. -/
theorem X1Split85A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X1Split85A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0_pairs. -/
theorem X1Split85A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split85A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1_pairs. -/
theorem X1Split85A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split85A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A2X0Y0Certs : List (Nat × Nat) := [
  (333, 0), (1124, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0Y0_check. -/
theorem X1Split85A2X0Y0_check : checkGrid m4TX1 2 985062231 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0Y0_pairs. -/
theorem X1Split85A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X1Split85A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0_pairs. -/
theorem X1Split85A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split85A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2_pairs. -/
theorem X1Split85A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split85A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A3X0Y0Certs : List (Nat × Nat) := [
  (88, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0Y0_check. -/
theorem X1Split85A3X0Y0_check : checkGrid m4TX1 2 1071345064 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0Y0_pairs. -/
theorem X1Split85A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 5
    outerMasks0S256Chunk0 masks3S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks3S32768Chunk0_bound y hy)
  · exact X1Split85A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0_pairs. -/
theorem X1Split85A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks3S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split85A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3_pairs. -/
theorem X1Split85A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split85A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split85_check. -/
theorem X1Split85_check : checkSplit m4TX1 (5, 0, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split85A0_pairs x hx y hy hw
    · exact X1Split85A1_pairs x hx y hy hw
    · exact X1Split85A2_pairs x hx y hy hw
    · exact X1Split85A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A0X0Y0Certs : List (Nat × Nat) := [
  (1139, 0), (1161, 1851), (1921, 0), (2823, 1256), (2967, 0),
  (3124, 0), (3248, 0), (5242, 141), (6706, 0), (7111, 0),
  (7221, 0), (7745, 2542), (7912, 434), (10388, 2880), (11798, 280),
  (12230, 0), (12700, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A0X0Y0_check. -/
theorem X1Split86A0X0Y0_check : checkGrid m4TX1 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A0X0Y0_pairs. -/
theorem X1Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A0X0_pairs. -/
theorem X1Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A0_pairs. -/
theorem X1Split86A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split86A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A1X0Y0Certs : List (Nat × Nat) := [
  (180, 996), (5036, 1526), (8933, 0), (11517, 0), (11837, 0),
  (11986, 0), (12749, 704)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A1X0Y0_check. -/
theorem X1Split86A1X0Y0_check : checkGrid m4TX1 2 91076351 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A1X0Y0_pairs. -/
theorem X1Split86A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split86A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A1X0_pairs. -/
theorem X1Split86A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A1_pairs. -/
theorem X1Split86A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split86A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A2X0Y0Certs : List (Nat × Nat) := [
  (935, 0), (2449, 0), (5840, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A2X0Y0_check. -/
theorem X1Split86A2X0Y0_check : checkGrid m4TX1 2 985062231 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A2X0Y0_pairs. -/
theorem X1Split86A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split86A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A2X0_pairs. -/
theorem X1Split86A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A2_pairs. -/
theorem X1Split86A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split86A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A3X0Y0_check. -/
theorem X1Split86A3X0Y0_check : checkGrid m4TX1 2 1071345064 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A3X0Y0_pairs. -/
theorem X1Split86A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 5
    outerMasks1S256Chunk0 masks2S4096Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S4096Chunk0_bound y hy)
  · exact X1Split86A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A3X0_pairs. -/
theorem X1Split86A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86A3_pairs. -/
theorem X1Split86A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split86A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split86_check. -/
theorem X1Split86_check : checkSplit m4TX1 (5, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split86A0_pairs x hx y hy hw
    · exact X1Split86A1_pairs x hx y hy hw
    · exact X1Split86A2_pairs x hx y hy hw
    · exact X1Split86A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split87A0X0Y0Certs : List (Nat × Nat) := [
  (147, 2569), (2407, 130), (2449, 0), (2621, 294), (3048, 829),
  (4265, 0), (4570, 243), (4704, 1766), (4727, 0), (5323, 417),
  (5597, 725), (5786, 0), (5791, 0), (6057, 0), (7465, 0),
  (7857, 0), (8084, 0), (8266, 635), (8541, 0), (8659, 962),
  (8933, 1566), (9411, 0), (9574, 0), (9662, 28), (9697, 0),
  (9927, 0), (10354, 0), (10967, 0), (11067, 0), (11304, 0),
  (11332, 1397), (11951, 0), (12033, 0), (12126, 107), (12173, 0),
  (12881, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0X0Y0_check. -/
theorem X1Split87A0X0Y0_check : checkGrid m4TX1 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0X0Y0_pairs. -/
theorem X1Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0X0_pairs. -/
theorem X1Split87A0X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0_pairs. -/
theorem X1Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split87A1X0Y0Certs : List (Nat × Nat) := [
  (633, 39), (1002, 350), (1955, 78), (9272, 0), (11318, 0),
  (11599, 0), (12356, 2265), (12579, 0), (12623, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1X0Y0_check. -/
theorem X1Split87A1X0Y0_check : checkGrid m4TX1 2 91076351 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1X0Y0_pairs. -/
theorem X1Split87A1X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1X0_pairs. -/
theorem X1Split87A1X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1_pairs. -/
theorem X1Split87A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split87A2X0Y0Certs : List (Nat × Nat) := [
  (84, 0), (779, 3159), (1728, 0), (2977, 0), (4617, 0),
  (6110, 0), (6180, 3), (6503, 0), (8111, 0), (9447, 0),
  (9527, 0), (9661, 0), (11873, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2X0Y0_check. -/
theorem X1Split87A2X0Y0_check : checkGrid m4TX1 2 985062231 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2X0Y0_pairs. -/
theorem X1Split87A2X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2X0_pairs. -/
theorem X1Split87A2X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2_pairs. -/
theorem X1Split87A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split87A3X0Y0Certs : List (Nat × Nat) := [
  (9022, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3X0Y0_check. -/
theorem X1Split87A3X0Y0_check : checkGrid m4TX1 2 1071345064 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3X0Y0_pairs. -/
theorem X1Split87A3X0Y0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 5
    outerMasks2S4096Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S4096Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S4096Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3X0_pairs. -/
theorem X1Split87A3X0_pairs : ∀ x ∈ outerMasks2S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3_pairs. -/
theorem X1Split87A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split87_check. -/
theorem X1Split87_check : checkSplit m4TX1 (5, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split87A0_pairs x hx y hy hw
    · exact X1Split87A1_pairs x hx y hy hw
    · exact X1Split87A2_pairs x hx y hy hw
    · exact X1Split87A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A0X0Y0Certs : List (Nat × Nat) := [
  (180, 0), (1982, 0), (2598, 0), (3147, 0), (3739, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X0Y0_check. -/
theorem X1Split88A0X0Y0_check : checkGrid m4TX1 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X0Y0_pairs. -/
theorem X1Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X0_pairs. -/
theorem X1Split88A0X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0_pairs. -/
theorem X1Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split88A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A1X0Y0Certs : List (Nat × Nat) := [
  (3316, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X0Y0_check. -/
theorem X1Split88A1X0Y0_check : checkGrid m4TX1 2 91076351 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X0Y0_pairs. -/
theorem X1Split88A1X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X0_pairs. -/
theorem X1Split88A1X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1_pairs. -/
theorem X1Split88A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split88A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A2X0Y0Certs : List (Nat × Nat) := [
  (593, 0), (2217, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X0Y0_check. -/
theorem X1Split88A2X0Y0_check : checkGrid m4TX1 2 985062231 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X0Y0_pairs. -/
theorem X1Split88A2X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X0_pairs. -/
theorem X1Split88A2X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2_pairs. -/
theorem X1Split88A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split88A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X0Y0_check. -/
theorem X1Split88A3X0Y0_check : checkGrid m4TX1 2 1071345064 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X0Y0_pairs. -/
theorem X1Split88A3X0Y0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 5
    outerMasks3S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks3S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X0_pairs. -/
theorem X1Split88A3X0_pairs : ∀ x ∈ outerMasks3S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3_pairs. -/
theorem X1Split88A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split88A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split88_check. -/
theorem X1Split88_check : checkSplit m4TX1 (5, 3, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split88A0_pairs x hx y hy hw
    · exact X1Split88A1_pairs x hx y hy hw
    · exact X1Split88A2_pairs x hx y hy hw
    · exact X1Split88A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A0X0Y0Certs : List (Nat × Nat) := [
  (44, 229), (191, 1110), (224, 1303), (230, 1361), (301, 2037),
  (304, 2045), (382, 2873)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A0X0Y0_check. -/
theorem X1Split89A0X0Y0_check : checkGrid m4TX1 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A0X0Y0_pairs. -/
theorem X1Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A0X0_pairs. -/
theorem X1Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A0_pairs. -/
theorem X1Split89A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split89A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A1X0Y0Certs : List (Nat × Nat) := [
  (113, 583), (119, 613)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A1X0Y0_check. -/
theorem X1Split89A1X0Y0_check : checkGrid m4TX1 2 91076351 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A1X0Y0_pairs. -/
theorem X1Split89A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split89A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A1X0_pairs. -/
theorem X1Split89A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A1_pairs. -/
theorem X1Split89A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split89A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A2X0Y0Certs : List (Nat × Nat) := [
  (387, 2896)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A2X0Y0_check. -/
theorem X1Split89A2X0Y0_check : checkGrid m4TX1 2 985062231 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A2X0Y0_pairs. -/
theorem X1Split89A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split89A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A2X0_pairs. -/
theorem X1Split89A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A2_pairs. -/
theorem X1Split89A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split89A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A3X0Y0_check. -/
theorem X1Split89A3X0Y0_check : checkGrid m4TX1 2 1071345064 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A3X0Y0_pairs. -/
theorem X1Split89A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 6
    outerMasks0S256Chunk0 masks2S32768Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks2S32768Chunk0_bound y hy)
  · exact X1Split89A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A3X0_pairs. -/
theorem X1Split89A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89A3_pairs. -/
theorem X1Split89A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split89A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split89_check. -/
theorem X1Split89_check : checkSplit m4TX1 (6, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split89A0_pairs x hx y hy hw
    · exact X1Split89A1_pairs x hx y hy hw
    · exact X1Split89A2_pairs x hx y hy hw
    · exact X1Split89A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A0X0Y0Certs : List (Nat × Nat) := [
  (81, 0), (388, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0X0Y0_check. -/
theorem X1Split90A0X0Y0_check : checkGrid m4TX1 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0X0Y0_pairs. -/
theorem X1Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0X0_pairs. -/
theorem X1Split90A0X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0_pairs. -/
theorem X1Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A1X0Y0Certs : List (Nat × Nat) := [
  (785, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1X0Y0_check. -/
theorem X1Split90A1X0Y0_check : checkGrid m4TX1 2 91076351 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1X0Y0_pairs. -/
theorem X1Split90A1X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split90A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1X0_pairs. -/
theorem X1Split90A1X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1_pairs. -/
theorem X1Split90A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2X0Y0_check. -/
theorem X1Split90A2X0Y0_check : checkGrid m4TX1 2 985062231 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2X0Y0_pairs. -/
theorem X1Split90A2X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split90A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2X0_pairs. -/
theorem X1Split90A2X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2_pairs. -/
theorem X1Split90A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3X0Y0_check. -/
theorem X1Split90A3X0Y0_check : checkGrid m4TX1 2 1071345064 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3X0Y0_pairs. -/
theorem X1Split90A3X0Y0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masks1S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 6
    outerMasks1S4096Chunk0 masks1S4096Chunk0
    (gridWords outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S4096Chunk0 masks1S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S4096Chunk0_bound
    · exact masks1S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S4096Chunk0_bound y hy)
  · exact X1Split90A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3X0_pairs. -/
theorem X1Split90A3X0_pairs : ∀ x ∈ outerMasks1S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3_pairs. -/
theorem X1Split90A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split90_check. -/
theorem X1Split90_check : checkSplit m4TX1 (6, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split90A0_pairs x hx y hy hw
    · exact X1Split90A1_pairs x hx y hy hw
    · exact X1Split90A2_pairs x hx y hy hw
    · exact X1Split90A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0X0Y0_check. -/
theorem X1Split91A0X0Y0_check : checkGrid m4TX1 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0X0Y0_pairs. -/
theorem X1Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0X0_pairs. -/
theorem X1Split91A0X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0_pairs. -/
theorem X1Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A1X0Y0Certs : List (Nat × Nat) := [
  (232, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1X0Y0_check. -/
theorem X1Split91A1X0Y0_check : checkGrid m4TX1 2 91076351 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1X0Y0_pairs. -/
theorem X1Split91A1X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1X0_pairs. -/
theorem X1Split91A1X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1_pairs. -/
theorem X1Split91A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A2X0Y0Certs : List (Nat × Nat) := [
  (69, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2X0Y0_check. -/
theorem X1Split91A2X0Y0_check : checkGrid m4TX1 2 985062231 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2X0Y0_pairs. -/
theorem X1Split91A2X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2X0_pairs. -/
theorem X1Split91A2X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2_pairs. -/
theorem X1Split91A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3X0Y0_check. -/
theorem X1Split91A3X0Y0_check : checkGrid m4TX1 2 1071345064 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3X0Y0_pairs. -/
theorem X1Split91A3X0Y0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 6
    outerMasks2S32768Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S32768Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S32768Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks2S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3X0_pairs. -/
theorem X1Split91A3X0_pairs : ∀ x ∈ outerMasks2S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3_pairs. -/
theorem X1Split91A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split91_check. -/
theorem X1Split91_check : checkSplit m4TX1 (6, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split91A0_pairs x hx y hy hw
    · exact X1Split91A1_pairs x hx y hy hw
    · exact X1Split91A2_pairs x hx y hy hw
    · exact X1Split91A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0X0Y0_check. -/
theorem X1Split92A0X0Y0_check : checkGrid m4TX1 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0X0Y0_pairs. -/
theorem X1Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0X0_pairs. -/
theorem X1Split92A0X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0_pairs. -/
theorem X1Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1X0Y0_check. -/
theorem X1Split92A1X0Y0_check : checkGrid m4TX1 2 91076351 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1X0Y0_pairs. -/
theorem X1Split92A1X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split92A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1X0_pairs. -/
theorem X1Split92A1X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1_pairs. -/
theorem X1Split92A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2X0Y0_check. -/
theorem X1Split92A2X0Y0_check : checkGrid m4TX1 2 985062231 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2X0Y0_pairs. -/
theorem X1Split92A2X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split92A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2X0_pairs. -/
theorem X1Split92A2X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2_pairs. -/
theorem X1Split92A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3X0Y0_check. -/
theorem X1Split92A3X0Y0_check : checkGrid m4TX1 2 1071345064 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3X0Y0_pairs. -/
theorem X1Split92A3X0Y0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masks1S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 7
    outerMasks0S4096Chunk0 masks1S32768Chunk0
    (gridWords outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S4096Chunk0 masks1S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S4096Chunk0_bound
    · exact masks1S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S4096Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S32768Chunk0_bound y hy)
  · exact X1Split92A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3X0_pairs. -/
theorem X1Split92A3X0_pairs : ∀ x ∈ outerMasks0S4096Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3_pairs. -/
theorem X1Split92A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S4096_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split92_check. -/
theorem X1Split92_check : checkSplit m4TX1 (7, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split92A0_pairs x hx y hy hw
    · exact X1Split92A1_pairs x hx y hy hw
    · exact X1Split92A2_pairs x hx y hy hw
    · exact X1Split92A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0X0Y0_check. -/
theorem X1Split93A0X0Y0_check : checkGrid m4TX1 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0X0Y0_pairs. -/
theorem X1Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0X0_pairs. -/
theorem X1Split93A0X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0_pairs. -/
theorem X1Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1X0Y0_check. -/
theorem X1Split93A1X0Y0_check : checkGrid m4TX1 2 91076351 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1X0Y0_pairs. -/
theorem X1Split93A1X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split93A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1X0_pairs. -/
theorem X1Split93A1X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1_pairs. -/
theorem X1Split93A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2X0Y0_check. -/
theorem X1Split93A2X0Y0_check : checkGrid m4TX1 2 985062231 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2X0Y0_pairs. -/
theorem X1Split93A2X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split93A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2X0_pairs. -/
theorem X1Split93A2X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2_pairs. -/
theorem X1Split93A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3X0Y0_check. -/
theorem X1Split93A3X0Y0_check : checkGrid m4TX1 2 1071345064 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3X0Y0_pairs. -/
theorem X1Split93A3X0Y0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masks0S4096Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 7
    outerMasks1S32768Chunk0 masks0S4096Chunk0
    (gridWords outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S32768Chunk0 masks0S4096Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S32768Chunk0_bound
    · exact masks0S4096Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S4096Chunk0_bound y hy)
  · exact X1Split93A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3X0_pairs. -/
theorem X1Split93A3X0_pairs : ∀ x ∈ outerMasks1S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S4096_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S4096Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3_pairs. -/
theorem X1Split93A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split93_check. -/
theorem X1Split93_check : checkSplit m4TX1 (7, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split93A0_pairs x hx y hy hw
    · exact X1Split93A1_pairs x hx y hy hw
    · exact X1Split93A2_pairs x hx y hy hw
    · exact X1Split93A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0X0Y0_check. -/
theorem X1Split94A0X0Y0_check : checkGrid m4TX1 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0X0Y0_pairs. -/
theorem X1Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 8 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 2 0 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A0X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0X0_pairs. -/
theorem X1Split94A0X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 8 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0_pairs. -/
theorem X1Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 8 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1X0Y0_check. -/
theorem X1Split94A1X0Y0_check : checkGrid m4TX1 2 91076351 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1X0Y0_pairs. -/
theorem X1Split94A1X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 8 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 2 91076351 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A1X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split94A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1X0_pairs. -/
theorem X1Split94A1X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 8 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1_pairs. -/
theorem X1Split94A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 8 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2X0Y0_check. -/
theorem X1Split94A2X0Y0_check : checkGrid m4TX1 2 985062231 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2X0Y0_pairs. -/
theorem X1Split94A2X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 8 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 2 985062231 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A2X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split94A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2X0_pairs. -/
theorem X1Split94A2X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 8 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2_pairs. -/
theorem X1Split94A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 8 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3X0Y0_check. -/
theorem X1Split94A3X0Y0_check : checkGrid m4TX1 2 1071345064 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3X0Y0_pairs. -/
theorem X1Split94A3X0Y0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masks0S32768Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 8 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 2 1071345064 8
    outerMasks0S32768Chunk0 masks0S32768Chunk0
    (gridWords outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A3X0Y0Certs
  · decide
  · decide
  · decide
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S32768Chunk0 masks0S32768Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S32768Chunk0_bound
    · exact masks0S32768Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S32768Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S32768Chunk0_bound y hy)
  · exact X1Split94A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3X0_pairs. -/
theorem X1Split94A3X0_pairs : ∀ x ∈ outerMasks0S32768Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 8 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S32768_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3_pairs. -/
theorem X1Split94A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 8 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S32768_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S32768Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for X1Split94_check. -/
theorem X1Split94_check : checkSplit m4TX1 (8, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X1Split94A0_pairs x hx y hy hw
    · exact X1Split94A1_pairs x hx y hy hw
    · exact X1Split94A2_pairs x hx y hy hw
    · exact X1Split94A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default heartbeat budget.
/-- Kernel-checked certificate for checkAll_X1. -/
theorem checkAll_X1 : checkAll m4TX1 splitsX1 = true := by
  simp only [checkAll, splitsX1, List.all_cons, List.all_nil,
    X1Split0_check, X1Split1_check, X1Split2_check, X1Split3_check,
    X1Split4_check, X1Split5_check, X1Split6_check, X1Split7_check,
    X1Split8_check, X1Split9_check, X1Split10_check, X1Split11_check,
    X1Split12_check, X1Split13_check, X1Split14_check, X1Split15_check,
    X1Split16_check, X1Split17_check, X1Split18_check, X1Split19_check,
    X1Split20_check, X1Split21_check, X1Split22_check, X1Split23_check,
    X1Split24_check, X1Split25_check, X1Split26_check, X1Split27_check,
    X1Split28_check, X1Split29_check, X1Split30_check, X1Split31_check,
    X1Split32_check, X1Split33_check, X1Split34_check, X1Split35_check,
    X1Split36_check, X1Split37_check, X1Split38_check, X1Split39_check,
    X1Split40_check, X1Split41_check, X1Split42_check, X1Split43_check,
    X1Split44_check, X1Split45_check, X1Split46_check, X1Split47_check,
    X1Split48_check, X1Split49_check, X1Split50_check, X1Split51_check,
    X1Split52_check, X1Split53_check, X1Split54_check, X1Split55_check,
    X1Split56_check, X1Split57_check, X1Split58_check, X1Split59_check,
    X1Split60_check, X1Split61_check, X1Split62_check, X1Split63_check,
    X1Split64_check, X1Split65_check, X1Split66_check, X1Split67_check,
    X1Split68_check, X1Split69_check, X1Split70_check, X1Split71_check,
    X1Split72_check, X1Split73_check, X1Split74_check, X1Split75_check,
    X1Split76_check, X1Split77_check, X1Split78_check, X1Split79_check,
    X1Split80_check, X1Split81_check, X1Split82_check, X1Split83_check,
    X1Split84_check, X1Split85_check, X1Split86_check, X1Split87_check,
    X1Split88_check, X1Split89_check, X1Split90_check, X1Split91_check,
    X1Split92_check, X1Split93_check, X1Split94_check, Bool.and_true]

#print axioms checkAll_X1

end Quantum.Stabilizer.Homological.LP.M150

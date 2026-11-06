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
def X1Split0A0X0Y0Certs : List (Nat × Nat) := [
  (0, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0X0Y0_check. -/
theorem X1Split0A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 0
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split0A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0X0Y0_pairs. -/
theorem X1Split0A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 0 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 0
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split0A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split0A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0X0_pairs. -/
theorem X1Split0A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 0 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split0A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split0A0_pairs. -/
theorem X1Split0A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 0 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split0A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split1A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0X0Y0_check. -/
theorem X1Split1A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split1A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0X0Y0_pairs. -/
theorem X1Split1A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split1A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split1A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0X0_pairs. -/
theorem X1Split1A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split1A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split1A0_pairs. -/
theorem X1Split1A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split1A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split2A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0X0Y0_check. -/
theorem X1Split2A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 1
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split2A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0X0Y0_pairs. -/
theorem X1Split2A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 1
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split2A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split2A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0X0_pairs. -/
theorem X1Split2A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split2A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split2A0_pairs. -/
theorem X1Split2A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split2A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split3A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0X0Y0_check. -/
theorem X1Split3A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split3A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0X0Y0_pairs. -/
theorem X1Split3A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split3A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split3A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0X0_pairs. -/
theorem X1Split3A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split3A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split3A0_pairs. -/
theorem X1Split3A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split3A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split4A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0X0Y0_check. -/
theorem X1Split4A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 1
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split4A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0X0Y0_pairs. -/
theorem X1Split4A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 1 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 1
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split4A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split4A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0X0_pairs. -/
theorem X1Split4A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 1 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split4A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split4A0_pairs. -/
theorem X1Split4A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 1 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split4A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split5A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0X0Y0_check. -/
theorem X1Split5A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 1
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split5A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0X0Y0_pairs. -/
theorem X1Split5A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 1
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split5A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split5A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0X0_pairs. -/
theorem X1Split5A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split5A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split5A0_pairs. -/
theorem X1Split5A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 1 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split5A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0X0Y0_check. -/
theorem X1Split6A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0X0Y0_pairs. -/
theorem X1Split6A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split6A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0X0_pairs. -/
theorem X1Split6A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A0_pairs. -/
theorem X1Split6A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1X0Y0_check. -/
theorem X1Split6A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1X0Y0_pairs. -/
theorem X1Split6A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split6A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1X0_pairs. -/
theorem X1Split6A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A1_pairs. -/
theorem X1Split6A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2X0Y0_check. -/
theorem X1Split6A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2X0Y0_pairs. -/
theorem X1Split6A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split6A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2X0_pairs. -/
theorem X1Split6A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A2_pairs. -/
theorem X1Split6A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split6A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3X0Y0_check. -/
theorem X1Split6A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3X0Y0_pairs. -/
theorem X1Split6A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 2
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split6A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split6A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3X0_pairs. -/
theorem X1Split6A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split6A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split6A3_pairs. -/
theorem X1Split6A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split6A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split7A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0X0Y0_check. -/
theorem X1Split7A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split7A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0X0Y0_pairs. -/
theorem X1Split7A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split7A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split7A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0X0_pairs. -/
theorem X1Split7A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split7A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split7A0_pairs. -/
theorem X1Split7A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split7A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split8A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0X0Y0_check. -/
theorem X1Split8A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split8A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0X0Y0_pairs. -/
theorem X1Split8A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split8A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split8A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0X0_pairs. -/
theorem X1Split8A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split8A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split8A0_pairs. -/
theorem X1Split8A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split8A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split9A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split9A0X0Y0_check. -/
theorem X1Split9A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 2
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split9A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split9A0X0Y0_pairs. -/
theorem X1Split9A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 2
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split9A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split9A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split9A0X0_pairs. -/
theorem X1Split9A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split9A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split10A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0X0Y0_check. -/
theorem X1Split10A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split10A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0X0Y0_pairs. -/
theorem X1Split10A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split10A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split10A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0X0_pairs. -/
theorem X1Split10A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split10A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split10A0_pairs. -/
theorem X1Split10A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split10A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split11A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0X0Y0_check. -/
theorem X1Split11A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split11A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0X0Y0_pairs. -/
theorem X1Split11A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split11A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split11A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0X0_pairs. -/
theorem X1Split11A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split11A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split11A0_pairs. -/
theorem X1Split11A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split11A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split12A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0X0Y0_check. -/
theorem X1Split12A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split12A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0X0Y0_pairs. -/
theorem X1Split12A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split12A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split12A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0X0_pairs. -/
theorem X1Split12A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split12A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split12A0_pairs. -/
theorem X1Split12A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split12A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split13A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0X0Y0_check. -/
theorem X1Split13A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split13A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0X0Y0_pairs. -/
theorem X1Split13A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split13A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split13A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0X0_pairs. -/
theorem X1Split13A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split13A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split13A0_pairs. -/
theorem X1Split13A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split13A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split14A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0X0Y0_check. -/
theorem X1Split14A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split14A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0X0Y0_pairs. -/
theorem X1Split14A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split14A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split14A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0X0_pairs. -/
theorem X1Split14A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split14A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split14A0_pairs. -/
theorem X1Split14A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split14A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split15A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0X0Y0_check. -/
theorem X1Split15A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split15A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0X0Y0_pairs. -/
theorem X1Split15A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split15A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split15A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0X0_pairs. -/
theorem X1Split15A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split15A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split15A0_pairs. -/
theorem X1Split15A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split15A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

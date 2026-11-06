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
def X0Split80A0X0Y0Certs : List (Nat × Nat) := [
  (240, 872), (757, 1989)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X0Y0_check. -/
theorem X0Split80A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X0Y0_pairs. -/
theorem X0Split80A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X0_pairs. -/
theorem X0Split80A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X1Y0Certs : List (Nat × Nat) := [
  (267, 1156), (514, 1470), (742, 1473), (904, 1485)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X1Y0_check. -/
theorem X0Split80A0X1Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X1Y0_pairs. -/
theorem X0Split80A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X1_pairs. -/
theorem X0Split80A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X2Y0Certs : List (Nat × Nat) := [
  (1142, 775)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X2Y0_check. -/
theorem X0Split80A0X2Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X2Y0_pairs. -/
theorem X0Split80A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X2Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk2 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X2_pairs. -/
theorem X0Split80A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X3Y0Certs : List (Nat × Nat) := [
  (63, 1943), (414, 865)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X3Y0_check. -/
theorem X0Split80A0X3Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X3Y0_pairs. -/
theorem X0Split80A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X3Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk3 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X3_pairs. -/
theorem X0Split80A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X4Y0Certs : List (Nat × Nat) := [
  (39, 1988), (805, 1808)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X4Y0_check. -/
theorem X0Split80A0X4Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X4Y0_pairs. -/
theorem X0Split80A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X4Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk4 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X4_pairs. -/
theorem X0Split80A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X5Y0Certs : List (Nat × Nat) := [
  (942, 838), (1475, 1519)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X5Y0_check. -/
theorem X0Split80A0X5Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X5Y0_pairs. -/
theorem X0Split80A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X5Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk5 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X5_pairs. -/
theorem X0Split80A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X6Y0Certs : List (Nat × Nat) := [
  (752, 333), (1112, 1758), (1586, 1953)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X6Y0_check. -/
theorem X0Split80A0X6Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X6Y0_pairs. -/
theorem X0Split80A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X6Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk6 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X6_pairs. -/
theorem X0Split80A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X7Y0Certs : List (Nat × Nat) := [
  (1083, 1336), (1438, 1813)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X7Y0_check. -/
theorem X0Split80A0X7Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X7Y0_pairs. -/
theorem X0Split80A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X7Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk7 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X7_pairs. -/
theorem X0Split80A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X8Y0Certs : List (Nat × Nat) := [
  (404, 1579), (1270, 103), (1443, 1039)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X8Y0_check. -/
theorem X0Split80A0X8Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X8Y0_pairs. -/
theorem X0Split80A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X8Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk8 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X8_pairs. -/
theorem X0Split80A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X9Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X9Y0_check. -/
theorem X0Split80A0X9Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X9Y0_pairs. -/
theorem X0Split80A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X9Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk9 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X9_pairs. -/
theorem X0Split80A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X10Y0Certs : List (Nat × Nat) := [
  (397, 847), (520, 1333), (828, 1157), (1606, 660), (1830, 1295),
  (1877, 1863)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X10Y0_check. -/
theorem X0Split80A0X10Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X10Y0_pairs. -/
theorem X0Split80A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X10Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk10 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X10_pairs. -/
theorem X0Split80A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X11Y0_check. -/
theorem X0Split80A0X11Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X11Y0_pairs. -/
theorem X0Split80A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X11Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk11 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X11_pairs. -/
theorem X0Split80A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X12Y0Certs : List (Nat × Nat) := [
  (721, 1746), (1344, 700), (1461, 1393), (1936, 699)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X12Y0_check. -/
theorem X0Split80A0X12Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X12Y0_pairs. -/
theorem X0Split80A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X12Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk12 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X12_pairs. -/
theorem X0Split80A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X13Y0Certs : List (Nat × Nat) := [
  (266, 1441), (700, 440)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X13Y0_check. -/
theorem X0Split80A0X13Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X13Y0_pairs. -/
theorem X0Split80A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X13Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk13 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X13_pairs. -/
theorem X0Split80A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X14Y0Certs : List (Nat × Nat) := [
  (1254, 1883), (1422, 1583)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X14Y0_check. -/
theorem X0Split80A0X14Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X14Y0_pairs. -/
theorem X0Split80A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X14Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk14 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X14_pairs. -/
theorem X0Split80A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X15Y0Certs : List (Nat × Nat) := [
  (523, 287), (815, 617)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X15Y0_check. -/
theorem X0Split80A0X15Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X15Y0_pairs. -/
theorem X0Split80A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X15Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk15 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X15_pairs. -/
theorem X0Split80A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X16Y0Certs : List (Nat × Nat) := [
  (157, 1211), (166, 1454), (1581, 883), (1677, 750), (1886, 911)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X16Y0_check. -/
theorem X0Split80A0X16Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X16Y0_pairs. -/
theorem X0Split80A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X16Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk16 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X16_pairs. -/
theorem X0Split80A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split80A0X17Y0Certs : List (Nat × Nat) := [
  (62, 1759), (1054, 1210), (1075, 1280)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X17Y0_check. -/
theorem X0Split80A0X17Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X17Y0_pairs. -/
theorem X0Split80A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split80A0X17Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk17 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split80A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0X17_pairs. -/
theorem X0Split80A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split80A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split80A0_pairs. -/
theorem X0Split80A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split80A0X0_pairs x hx y hy hw
  · exact X0Split80A0X1_pairs x hx y hy hw
  · exact X0Split80A0X2_pairs x hx y hy hw
  · exact X0Split80A0X3_pairs x hx y hy hw
  · exact X0Split80A0X4_pairs x hx y hy hw
  · exact X0Split80A0X5_pairs x hx y hy hw
  · exact X0Split80A0X6_pairs x hx y hy hw
  · exact X0Split80A0X7_pairs x hx y hy hw
  · exact X0Split80A0X8_pairs x hx y hy hw
  · exact X0Split80A0X9_pairs x hx y hy hw
  · exact X0Split80A0X10_pairs x hx y hy hw
  · exact X0Split80A0X11_pairs x hx y hy hw
  · exact X0Split80A0X12_pairs x hx y hy hw
  · exact X0Split80A0X13_pairs x hx y hy hw
  · exact X0Split80A0X14_pairs x hx y hy hw
  · exact X0Split80A0X15_pairs x hx y hy hw
  · exact X0Split80A0X16_pairs x hx y hy hw
  · exact X0Split80A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X0Y0Certs : List (Nat × Nat) := [
  (43612, 1955), (47431, 920)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X0Y0_check. -/
theorem X0Split81A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X0Y0_pairs. -/
theorem X0Split81A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X0_pairs. -/
theorem X0Split81A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X1Y0_check. -/
theorem X0Split81A0X1Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X1Y0_pairs. -/
theorem X0Split81A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X1_pairs. -/
theorem X0Split81A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X2Y0Certs : List (Nat × Nat) := [
  (38350, 1041)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X2Y0_check. -/
theorem X0Split81A0X2Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X2Y0_pairs. -/
theorem X0Split81A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X2Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk2 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X2_pairs. -/
theorem X0Split81A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X3Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X3Y0_check. -/
theorem X0Split81A0X3Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X3Y0_pairs. -/
theorem X0Split81A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X3Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk3 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X3_pairs. -/
theorem X0Split81A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X4Y0Certs : List (Nat × Nat) := [
  (9695, 523), (14426, 596), (18686, 1463), (24364, 1408)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X4Y0_check. -/
theorem X0Split81A0X4Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X4Y0_pairs. -/
theorem X0Split81A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X4Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk4 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X4_pairs. -/
theorem X0Split81A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X5Y0Certs : List (Nat × Nat) := [
  (17817, 1749), (22775, 1570), (44247, 1607)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X5Y0_check. -/
theorem X0Split81A0X5Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X5Y0_pairs. -/
theorem X0Split81A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X5Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk5 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X5_pairs. -/
theorem X0Split81A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X6Y0Certs : List (Nat × Nat) := [
  (50829, 917)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X6Y0_check. -/
theorem X0Split81A0X6Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X6Y0_pairs. -/
theorem X0Split81A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X6Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk6 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X6_pairs. -/
theorem X0Split81A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X7Y0Certs : List (Nat × Nat) := [
  (41116, 1586)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X7Y0_check. -/
theorem X0Split81A0X7Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X7Y0_pairs. -/
theorem X0Split81A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X7Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk7 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X7_pairs. -/
theorem X0Split81A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X8Y0Certs : List (Nat × Nat) := [
  (47717, 739)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X8Y0_check. -/
theorem X0Split81A0X8Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X8Y0_pairs. -/
theorem X0Split81A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X8Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk8 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X8_pairs. -/
theorem X0Split81A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X9Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X9Y0_check. -/
theorem X0Split81A0X9Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X9Y0_pairs. -/
theorem X0Split81A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X9Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk9 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X9_pairs. -/
theorem X0Split81A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X10Y0Certs : List (Nat × Nat) := [
  (37961, 354), (49259, 1123), (55919, 1848), (58390, 1942)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X10Y0_check. -/
theorem X0Split81A0X10Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X10Y0_pairs. -/
theorem X0Split81A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X10Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk10 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X10_pairs. -/
theorem X0Split81A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X11Y0_check. -/
theorem X0Split81A0X11Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X11Y0_pairs. -/
theorem X0Split81A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X11Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk11 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X11_pairs. -/
theorem X0Split81A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X12Y0Certs : List (Nat × Nat) := [
  (22714, 487), (34631, 425), (54795, 1486)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X12Y0_check. -/
theorem X0Split81A0X12Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X12Y0_pairs. -/
theorem X0Split81A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X12Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk12 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X12_pairs. -/
theorem X0Split81A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X13Y0Certs : List (Nat × Nat) := [
  (1246, 1563), (17475, 1402)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X13Y0_check. -/
theorem X0Split81A0X13Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X13Y0_pairs. -/
theorem X0Split81A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X13Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk13 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X13_pairs. -/
theorem X0Split81A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X14Y0Certs : List (Nat × Nat) := [
  (20303, 1051)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X14Y0_check. -/
theorem X0Split81A0X14Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X14Y0_pairs. -/
theorem X0Split81A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X14Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk14 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X14_pairs. -/
theorem X0Split81A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X15Y0Certs : List (Nat × Nat) := [
  (21203, 1272)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X15Y0_check. -/
theorem X0Split81A0X15Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X15Y0_pairs. -/
theorem X0Split81A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X15Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk15 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X15_pairs. -/
theorem X0Split81A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X16Y0Certs : List (Nat × Nat) := [
  (2901, 849), (15112, 1929), (54961, 210), (58239, 979)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X16Y0_check. -/
theorem X0Split81A0X16Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X16Y0_pairs. -/
theorem X0Split81A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X16Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk16 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X16_pairs. -/
theorem X0Split81A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split81A0X17Y0Certs : List (Nat × Nat) := [
  (9917, 861), (31191, 1666)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X17Y0_check. -/
theorem X0Split81A0X17Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X17Y0_pairs. -/
theorem X0Split81A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split81A0X17Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks4S2048Chunk17 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X0M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split81A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0X17_pairs. -/
theorem X0Split81A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split81A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split81A0_pairs. -/
theorem X0Split81A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split81A0X0_pairs x hx y hy hw
  · exact X0Split81A0X1_pairs x hx y hy hw
  · exact X0Split81A0X2_pairs x hx y hy hw
  · exact X0Split81A0X3_pairs x hx y hy hw
  · exact X0Split81A0X4_pairs x hx y hy hw
  · exact X0Split81A0X5_pairs x hx y hy hw
  · exact X0Split81A0X6_pairs x hx y hy hw
  · exact X0Split81A0X7_pairs x hx y hy hw
  · exact X0Split81A0X8_pairs x hx y hy hw
  · exact X0Split81A0X9_pairs x hx y hy hw
  · exact X0Split81A0X10_pairs x hx y hy hw
  · exact X0Split81A0X11_pairs x hx y hy hw
  · exact X0Split81A0X12_pairs x hx y hy hw
  · exact X0Split81A0X13_pairs x hx y hy hw
  · exact X0Split81A0X14_pairs x hx y hy hw
  · exact X0Split81A0X15_pairs x hx y hy hw
  · exact X0Split81A0X16_pairs x hx y hy hw
  · exact X0Split81A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X0Y0_check. -/
theorem X0Split82A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X0Y0_pairs. -/
theorem X0Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A0X1Y0Certs : List (Nat × Nat) := [
  (3110, 251), (3114, 268), (6189, 361), (6759, 0), (7891, 0),
  (8017, 0), (8330, 252), (8607, 1418), (12300, 454), (12390, 0),
  (12475, 1167), (14963, 643), (15167, 1644), (18149, 0), (24497, 507),
  (24770, 1839), (26993, 0), (27343, 0), (28855, 0), (30804, 1512),
  (31455, 489), (32925, 0), (33610, 0), (34482, 0), (35453, 0),
  (36574, 143), (36675, 490), (36765, 0), (38280, 0), (38299, 0),
  (38395, 0), (39769, 669), (39817, 0), (47803, 0), (48039, 0),
  (48258, 0), (48437, 552), (48445, 585), (48888, 0), (49216, 0),
  (50140, 0), (51512, 666), (51534, 753), (51656, 0), (53328, 1010),
  (55117, 1247), (55231, 1871), (56292, 0), (57922, 0), (58588, 0),
  (58804, 0), (59416, 1005), (59563, 1773), (60964, 250), (61157, 1008),
  (64004, 0), (65970, 0), (67338, 0), (67706, 0), (67757, 0),
  (68135, 1087), (68773, 0), (69041, 0), (69593, 0), (70124, 336),
  (71461, 0), (74454, 0), (75139, 0), (75362, 0), (76750, 0),
  (77750, 1301), (79064, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X1Y0_check. -/
theorem X0Split82A0X1Y0_check : checkGrid m4TX0 censusX0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A0X1Y0_pairs. -/
theorem X0Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A1X0Y0Certs : List (Nat × Nat) := [
  (2763, 565), (22295, 400), (22511, 1362), (38003, 0), (40441, 1870),
  (52237, 0), (55576, 1370), (56884, 0), (67911, 0), (69332, 0),
  (91541, 726), (94981, 549), (108369, 213)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X0Y0_check. -/
theorem X0Split82A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X0Y0_pairs. -/
theorem X0Split82A1X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A1X1Y0Certs : List (Nat × Nat) := [
  (19902, 1363), (34694, 0), (39686, 0), (39748, 592), (47938, 0),
  (49776, 0), (57869, 0), (58075, 0), (68902, 0), (74813, 0),
  (74898, 302), (75095, 1088), (79037, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X1Y0_check. -/
theorem X0Split82A1X1Y0_check : checkGrid m4TX0 censusX0 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A1X1Y0_pairs. -/
theorem X0Split82A1X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A1X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A2X0Y0Certs : List (Nat × Nat) := [
  (1176, 0), (5472, 984), (5857, 0), (6843, 0), (21159, 1107),
  (29049, 0), (29896, 0), (52650, 0), (56538, 0), (61745, 0),
  (65057, 924), (65226, 1842), (75025, 0), (81098, 0), (90724, 0),
  (92354, 0), (94720, 0), (97022, 0), (99879, 0), (108610, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X0Y0_check. -/
theorem X0Split82A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X0Y0_pairs. -/
theorem X0Split82A2X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A2X1Y0Certs : List (Nat × Nat) := [
  (6509, 1860), (27545, 0), (29773, 729), (29940, 1525), (30702, 0),
  (32645, 104), (39067, 0), (39615, 0), (53222, 553), (58438, 0),
  (66533, 1846), (68221, 1528), (77723, 1163)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X1Y0_check. -/
theorem X0Split82A2X1Y0_check : checkGrid m4TX0 censusX0 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A2X1Y0_pairs. -/
theorem X0Split82A2X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A2X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A3X0Y0Certs : List (Nat × Nat) := [
  (34118, 0), (58441, 0), (80901, 0), (98083, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X0Y0_check. -/
theorem X0Split82A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X0Y0_pairs. -/
theorem X0Split82A3X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split82A3X1Y0Certs : List (Nat × Nat) := [
  (31555, 903), (48952, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X1Y0_check. -/
theorem X0Split82A3X1Y0_check : checkGrid m4TX0 censusX0 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split82A3X1Y0_pairs. -/
theorem X0Split82A3X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split82A3X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X0Y0Certs : List (Nat × Nat) := [
  (33208, 1653), (42489, 150)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X0Y0_check. -/
theorem X0Split83A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X0Y0_pairs. -/
theorem X0Split83A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X0_pairs. -/
theorem X0Split83A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X1Y0Certs : List (Nat × Nat) := [
  (11088, 562), (11422, 889), (32530, 188)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X1Y0_check. -/
theorem X0Split83A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X1Y0_pairs. -/
theorem X0Split83A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X1_pairs. -/
theorem X0Split83A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X2Y0Certs : List (Nat × Nat) := [
  (1975, 1225), (9556, 442), (36502, 886), (50091, 786), (51857, 493)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X2Y0_check. -/
theorem X0Split83A0X2Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X2Y0_pairs. -/
theorem X0Split83A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X2Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk2 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X2_pairs. -/
theorem X0Split83A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X3Y0Certs : List (Nat × Nat) := [
  (6255, 380), (14067, 1493), (16058, 133)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X3Y0_check. -/
theorem X0Split83A0X3Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X3Y0_pairs. -/
theorem X0Split83A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X3Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk3 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X3_pairs. -/
theorem X0Split83A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X4Y0Certs : List (Nat × Nat) := [
  (2674, 49), (4516, 444), (10695, 384)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X4Y0_check. -/
theorem X0Split83A0X4Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X4Y0_pairs. -/
theorem X0Split83A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X4Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk4 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X4_pairs. -/
theorem X0Split83A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X5Y0Certs : List (Nat × Nat) := [
  (5985, 382), (13426, 450), (26237, 502), (30047, 501), (35010, 5),
  (36326, 1356)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X5Y0_check. -/
theorem X0Split83A0X5Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X5Y0_pairs. -/
theorem X0Split83A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X5Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk5 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X5_pairs. -/
theorem X0Split83A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X6Y0Certs : List (Nat × Nat) := [
  (2394, 1094), (7665, 385), (8967, 1494), (38941, 8), (44716, 452)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X6Y0_check. -/
theorem X0Split83A0X6Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X6Y0_pairs. -/
theorem X0Split83A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X6Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk6 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X6_pairs. -/
theorem X0Split83A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X7Y0Certs : List (Nat × Nat) := [
  (4452, 256), (6215, 69), (13831, 11), (35573, 992), (37436, 1352)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X7Y0_check. -/
theorem X0Split83A0X7Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X7Y0_pairs. -/
theorem X0Split83A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X7Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk7 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X7_pairs. -/
theorem X0Split83A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X8Y0Certs : List (Nat × Nat) := [
  (16977, 1498), (23961, 790), (40445, 70), (41489, 1820), (45224, 345)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X8Y0_check. -/
theorem X0Split83A0X8Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X8Y0_pairs. -/
theorem X0Split83A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X8Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk8 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X8_pairs. -/
theorem X0Split83A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X9Y0Certs : List (Nat × Nat) := [
  (1714, 47), (3776, 1353), (4933, 294)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X9Y0_check. -/
theorem X0Split83A0X9Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X9Y0_pairs. -/
theorem X0Split83A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X9Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk9 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X9_pairs. -/
theorem X0Split83A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X10Y0Certs : List (Nat × Nat) := [
  (10811, 221), (17860, 190), (21053, 989), (23511, 792), (39652, 895)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X10Y0_check. -/
theorem X0Split83A0X10Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X10Y0_pairs. -/
theorem X0Split83A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X10Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk10 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X10_pairs. -/
theorem X0Split83A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X11Y0Certs : List (Nat × Nat) := [
  (3023, 1000), (10982, 26), (13145, 76)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X11Y0_check. -/
theorem X0Split83A0X11Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X11Y0_pairs. -/
theorem X0Split83A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X11Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk11 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X11_pairs. -/
theorem X0Split83A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X12Y0Certs : List (Nat × Nat) := [
  (8602, 890), (13443, 34), (27621, 794), (28811, 222), (30629, 1822),
  (35933, 991)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X12Y0_check. -/
theorem X0Split83A0X12Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X12Y0_pairs. -/
theorem X0Split83A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X12Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk12 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X12_pairs. -/
theorem X0Split83A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X13Y0Certs : List (Nat × Nat) := [
  (874, 48), (9634, 46)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X13Y0_check. -/
theorem X0Split83A0X13Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X13Y0_pairs. -/
theorem X0Split83A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X13Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk13 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X13_pairs. -/
theorem X0Split83A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X14Y0Certs : List (Nat × Nat) := [
  (7270, 181), (13960, 189), (19181, 218), (20509, 630), (20949, 152),
  (33816, 86), (47039, 1825), (47645, 73), (55469, 1821), (60001, 14)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X14Y0_check. -/
theorem X0Split83A0X14Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X14Y0_pairs. -/
theorem X0Split83A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X14Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk14 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X14_pairs. -/
theorem X0Split83A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X15Y0Certs : List (Nat × Nat) := [
  (2030, 716)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X15Y0_check. -/
theorem X0Split83A0X15Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X15Y0_pairs. -/
theorem X0Split83A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X15Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk15 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X15_pairs. -/
theorem X0Split83A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X16Y0Certs : List (Nat × Nat) := [
  (11199, 147), (29336, 1357), (39331, 18), (39697, 112), (55877, 503)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X16Y0_check. -/
theorem X0Split83A0X16Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X16Y0_pairs. -/
theorem X0Split83A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X16Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk16 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X16_pairs. -/
theorem X0Split83A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split83A0X17Y0Certs : List (Nat × Nat) := [
  (3971, 223), (12567, 1496), (41229, 151)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X17Y0_check. -/
theorem X0Split83A0X17Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X17Y0_pairs. -/
theorem X0Split83A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split83A0X17Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk17 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split83A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0X17_pairs. -/
theorem X0Split83A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split83A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split83A0_pairs. -/
theorem X0Split83A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split83A0X0_pairs x hx y hy hw
  · exact X0Split83A0X1_pairs x hx y hy hw
  · exact X0Split83A0X2_pairs x hx y hy hw
  · exact X0Split83A0X3_pairs x hx y hy hw
  · exact X0Split83A0X4_pairs x hx y hy hw
  · exact X0Split83A0X5_pairs x hx y hy hw
  · exact X0Split83A0X6_pairs x hx y hy hw
  · exact X0Split83A0X7_pairs x hx y hy hw
  · exact X0Split83A0X8_pairs x hx y hy hw
  · exact X0Split83A0X9_pairs x hx y hy hw
  · exact X0Split83A0X10_pairs x hx y hy hw
  · exact X0Split83A0X11_pairs x hx y hy hw
  · exact X0Split83A0X12_pairs x hx y hy hw
  · exact X0Split83A0X13_pairs x hx y hy hw
  · exact X0Split83A0X14_pairs x hx y hy hw
  · exact X0Split83A0X15_pairs x hx y hy hw
  · exact X0Split83A0X16_pairs x hx y hy hw
  · exact X0Split83A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X0Y0_check. -/
theorem X0Split84A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X0Y0_pairs. -/
theorem X0Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X0_pairs. -/
theorem X0Split84A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X1Y0_check. -/
theorem X0Split84A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X1Y0_pairs. -/
theorem X0Split84A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X1_pairs. -/
theorem X0Split84A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X2Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X2Y0_check. -/
theorem X0Split84A0X2Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X2Y0_pairs. -/
theorem X0Split84A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X2Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk2 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X2_pairs. -/
theorem X0Split84A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X3Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X3Y0_check. -/
theorem X0Split84A0X3Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X3Y0_pairs. -/
theorem X0Split84A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X3Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk3 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X3_pairs. -/
theorem X0Split84A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X4Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X4Y0_check. -/
theorem X0Split84A0X4Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X4Y0_pairs. -/
theorem X0Split84A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X4Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk4 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X4_pairs. -/
theorem X0Split84A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X5Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X5Y0_check. -/
theorem X0Split84A0X5Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X5Y0_pairs. -/
theorem X0Split84A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X5Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk5 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X5_pairs. -/
theorem X0Split84A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X6Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X6Y0_check. -/
theorem X0Split84A0X6Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X6Y0_pairs. -/
theorem X0Split84A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X6Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk6 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X6_pairs. -/
theorem X0Split84A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X7Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X7Y0_check. -/
theorem X0Split84A0X7Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X7Y0_pairs. -/
theorem X0Split84A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X7Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk7 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X7_pairs. -/
theorem X0Split84A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X8Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X8Y0_check. -/
theorem X0Split84A0X8Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X8Y0_pairs. -/
theorem X0Split84A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X8Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk8 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X8_pairs. -/
theorem X0Split84A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X9Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X9Y0_check. -/
theorem X0Split84A0X9Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X9Y0_pairs. -/
theorem X0Split84A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X9Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk9 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X9_pairs. -/
theorem X0Split84A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X10Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X10Y0_check. -/
theorem X0Split84A0X10Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X10Y0_pairs. -/
theorem X0Split84A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X10Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk10 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X10_pairs. -/
theorem X0Split84A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X11Y0_check. -/
theorem X0Split84A0X11Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X11Y0_pairs. -/
theorem X0Split84A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X11Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk11 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X11_pairs. -/
theorem X0Split84A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X12Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X12Y0_check. -/
theorem X0Split84A0X12Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X12Y0_pairs. -/
theorem X0Split84A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X12Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk12 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X12_pairs. -/
theorem X0Split84A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X13Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X13Y0_check. -/
theorem X0Split84A0X13Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X13Y0_pairs. -/
theorem X0Split84A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X13Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk13 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X13_pairs. -/
theorem X0Split84A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X14Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X14Y0_check. -/
theorem X0Split84A0X14Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X14Y0_pairs. -/
theorem X0Split84A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X14Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk14 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X14_pairs. -/
theorem X0Split84A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X15Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X15Y0_check. -/
theorem X0Split84A0X15Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X15Y0_pairs. -/
theorem X0Split84A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X15Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk15 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X15_pairs. -/
theorem X0Split84A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X16Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X16Y0_check. -/
theorem X0Split84A0X16Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X16Y0_pairs. -/
theorem X0Split84A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X16Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk16 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X16_pairs. -/
theorem X0Split84A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split84A0X17Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X17Y0_check. -/
theorem X0Split84A0X17Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X17Y0_pairs. -/
theorem X0Split84A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split84A0X17Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks4S2048Chunk17 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X0M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split84A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0X17_pairs. -/
theorem X0Split84A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split84A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split84A0_pairs. -/
theorem X0Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X0Split84A0X0_pairs x hx y hy hw
  · exact X0Split84A0X1_pairs x hx y hy hw
  · exact X0Split84A0X2_pairs x hx y hy hw
  · exact X0Split84A0X3_pairs x hx y hy hw
  · exact X0Split84A0X4_pairs x hx y hy hw
  · exact X0Split84A0X5_pairs x hx y hy hw
  · exact X0Split84A0X6_pairs x hx y hy hw
  · exact X0Split84A0X7_pairs x hx y hy hw
  · exact X0Split84A0X8_pairs x hx y hy hw
  · exact X0Split84A0X9_pairs x hx y hy hw
  · exact X0Split84A0X10_pairs x hx y hy hw
  · exact X0Split84A0X11_pairs x hx y hy hw
  · exact X0Split84A0X12_pairs x hx y hy hw
  · exact X0Split84A0X13_pairs x hx y hy hw
  · exact X0Split84A0X14_pairs x hx y hy hw
  · exact X0Split84A0X15_pairs x hx y hy hw
  · exact X0Split84A0X16_pairs x hx y hy hw
  · exact X0Split84A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A0X0Y0Certs : List (Nat × Nat) := [
  (145, 207), (165, 230), (229, 271), (586, 0), (647, 483),
  (688, 513), (781, 547), (1022, 665), (1304, 779), (1503, 868),
  (1505, 0), (1813, 1020), (1977, 1081)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0Y0_check. -/
theorem X0Split85A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0Y0_pairs. -/
theorem X0Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X0Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A0X0Y1Certs : List (Nat × Nat) := [
  (16, 1119), (412, 1282), (747, 0), (873, 1477), (883, 1480),
  (935, 1523), (1021, 0), (1196, 0), (1335, 1698), (1507, 1761),
  (1624, 0), (1733, 1869), (1858, 1916), (2034, 1994)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0Y1_check. -/
theorem X0Split85A0X0Y1_check : checkGrid m4TX0 censusX0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0Y1_pairs. -/
theorem X0Split85A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A0X0Y1Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X0Split85A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A0X0_pairs. -/
theorem X0Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X0Split85A0X0Y0_pairs x hx y hy hw
  · exact X0Split85A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A1X0Y0Certs : List (Nat × Nat) := [
  (14, 81), (533, 430), (859, 591), (1721, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0Y0_check. -/
theorem X0Split85A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0Y0_pairs. -/
theorem X0Split85A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X0Split85A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A1X0Y1Certs : List (Nat × Nat) := [
  (1018, 1552)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0Y1_check. -/
theorem X0Split85A1X0Y1_check : checkGrid m4TX0 censusX0 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A1X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0Y1_pairs. -/
theorem X0Split85A1X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A1X0Y1Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X0Split85A1X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A1X0_pairs. -/
theorem X0Split85A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X0Split85A1X0Y0_pairs x hx y hy hw
  · exact X0Split85A1X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A2X0Y0Certs : List (Nat × Nat) := [
  (198, 248), (1733, 976)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0Y0_check. -/
theorem X0Split85A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0Y0_pairs. -/
theorem X0Split85A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X0Split85A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A2X0Y1Certs : List (Nat × Nat) := [
  (15, 0), (134, 1162), (1223, 1642)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0Y1_check. -/
theorem X0Split85A2X0Y1_check : checkGrid m4TX0 censusX0 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A2X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0Y1_pairs. -/
theorem X0Split85A2X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A2X0Y1Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X0Split85A2X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A2X0_pairs. -/
theorem X0Split85A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X0Split85A2X0Y0_pairs x hx y hy hw
  · exact X0Split85A2X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A3X0Y0Certs : List (Nat × Nat) := [
  (1726, 973)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0Y0_check. -/
theorem X0Split85A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0Y0_pairs. -/
theorem X0Split85A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split85A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X0Split85A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split85A3X0Y1Certs : List (Nat × Nat) := [
  (85, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0Y1_check. -/
theorem X0Split85A3X0Y1_check : checkGrid m4TX0 censusX0 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A3X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0Y1_pairs. -/
theorem X0Split85A3X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns) X0Split85A3X0Y1Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X0Split85A3X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split85A3X0_pairs. -/
theorem X0Split85A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X0Split85A3X0Y0_pairs x hx y hy hw
  · exact X0Split85A3X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A0X0Y0_check. -/
theorem X0Split86A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A0X0Y0_pairs. -/
theorem X0Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A0X0_pairs. -/
theorem X0Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split86A1X0Y0Certs : List (Nat × Nat) := [
  (581, 531), (679, 933), (3050, 0), (4612, 1019), (4781, 1963),
  (6141, 0), (7326, 1550), (10159, 569), (11304, 0), (12653, 163),
  (12879, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A1X0Y0_check. -/
theorem X0Split86A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A1X0Y0_pairs. -/
theorem X0Split86A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split86A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A1X0_pairs. -/
theorem X0Split86A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split86A2X0Y0Certs : List (Nat × Nat) := [
  (664, 0), (2315, 512), (2546, 1592), (4196, 1114), (4774, 0),
  (5099, 0), (7524, 472), (7617, 830), (7861, 0), (9262, 464),
  (10251, 948), (10306, 0), (10435, 0), (10793, 0), (11870, 0),
  (12416, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A2X0Y0_check. -/
theorem X0Split86A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A2X0Y0_pairs. -/
theorem X0Split86A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split86A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A2X0_pairs. -/
theorem X0Split86A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split86A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A3X0Y0_check. -/
theorem X0Split86A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A3X0Y0_pairs. -/
theorem X0Split86A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split86A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split86A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split86A3X0_pairs. -/
theorem X0Split86A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split86A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A0X0Y0Certs : List (Nat × Nat) := [
  (1263, 0), (1583, 0), (1719, 0), (2739, 0), (5562, 0),
  (6437, 0), (8134, 0), (9291, 0), (9380, 0), (9582, 0),
  (9857, 0), (10241, 0), (10984, 0), (12173, 0), (12392, 0),
  (12660, 0), (12724, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0X0Y0_check. -/
theorem X0Split87A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0X0Y0_pairs. -/
theorem X0Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0X0_pairs. -/
theorem X0Split87A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A0_pairs. -/
theorem X0Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A1X0Y0Certs : List (Nat × Nat) := [
  (10466, 0), (11650, 0), (12348, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1X0Y0_check. -/
theorem X0Split87A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1X0Y0_pairs. -/
theorem X0Split87A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1X0_pairs. -/
theorem X0Split87A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A1_pairs. -/
theorem X0Split87A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A2X0Y0Certs : List (Nat × Nat) := [
  (1991, 0), (3191, 0), (3431, 0), (4170, 0), (4607, 0),
  (5862, 0), (6254, 0), (6363, 0), (9482, 0), (11090, 0),
  (11415, 0), (11619, 0), (12368, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2X0Y0_check. -/
theorem X0Split87A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2X0Y0_pairs. -/
theorem X0Split87A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2X0_pairs. -/
theorem X0Split87A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A2_pairs. -/
theorem X0Split87A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split87A3X0Y0Certs : List (Nat × Nat) := [
  (4439, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3X0Y0_check. -/
theorem X0Split87A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3X0Y0_pairs. -/
theorem X0Split87A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split87A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split87A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3X0_pairs. -/
theorem X0Split87A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split87A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split87A3_pairs. -/
theorem X0Split87A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split87A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A0X0Y0Certs : List (Nat × Nat) := [
  (180, 0), (1982, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X0Y0_check. -/
theorem X0Split88A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X0Y0_pairs. -/
theorem X0Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X0_pairs. -/
theorem X0Split88A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A0X1Y0Certs : List (Nat × Nat) := [
  (574, 0), (1123, 0), (1715, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X1Y0_check. -/
theorem X0Split88A0X1Y0_check : checkGrid m4TX0 censusX0 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X1Y0_pairs. -/
theorem X0Split88A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0X1_pairs. -/
theorem X0Split88A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A0_pairs. -/
theorem X0Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split88A0X0_pairs x hx y hy hw
  · exact X0Split88A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X0Y0_check. -/
theorem X0Split88A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X0Y0_pairs. -/
theorem X0Split88A1X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X0_pairs. -/
theorem X0Split88A1X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A1X1Y0Certs : List (Nat × Nat) := [
  (1292, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X1Y0_check. -/
theorem X0Split88A1X1Y0_check : checkGrid m4TX0 censusX0 2 91076351 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X1Y0_pairs. -/
theorem X0Split88A1X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A1X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1X1_pairs. -/
theorem X0Split88A1X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A1_pairs. -/
theorem X0Split88A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split88A1X0_pairs x hx y hy hw
  · exact X0Split88A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A2X0Y0Certs : List (Nat × Nat) := [
  (593, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X0Y0_check. -/
theorem X0Split88A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X0Y0_pairs. -/
theorem X0Split88A2X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X0_pairs. -/
theorem X0Split88A2X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A2X1Y0Certs : List (Nat × Nat) := [
  (193, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X1Y0_check. -/
theorem X0Split88A2X1Y0_check : checkGrid m4TX0 censusX0 2 985062231 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X1Y0_pairs. -/
theorem X0Split88A2X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A2X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2X1_pairs. -/
theorem X0Split88A2X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A2_pairs. -/
theorem X0Split88A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split88A2X0_pairs x hx y hy hw
  · exact X0Split88A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X0Y0_check. -/
theorem X0Split88A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X0Y0_pairs. -/
theorem X0Split88A3X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X0_pairs. -/
theorem X0Split88A3X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split88A3X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X1Y0_check. -/
theorem X0Split88A3X1Y0_check : checkGrid m4TX0 censusX0 2 1071345064 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X1Y0_pairs. -/
theorem X0Split88A3X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split88A3X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X0M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split88A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3X1_pairs. -/
theorem X0Split88A3X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split88A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split88A3_pairs. -/
theorem X0Split88A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split88A3X0_pairs x hx y hy hw
  · exact X0Split88A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A0X0Y0_check. -/
theorem X0Split89A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A0X0Y0_pairs. -/
theorem X0Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A0X0_pairs. -/
theorem X0Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A1X0Y0_check. -/
theorem X0Split89A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A1X0Y0_pairs. -/
theorem X0Split89A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split89A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A1X0_pairs. -/
theorem X0Split89A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A2X0Y0Certs : List (Nat × Nat) := [
  (19, 0), (115, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A2X0Y0_check. -/
theorem X0Split89A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A2X0Y0_pairs. -/
theorem X0Split89A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split89A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A2X0_pairs. -/
theorem X0Split89A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split89A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A3X0Y0_check. -/
theorem X0Split89A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A3X0Y0_pairs. -/
theorem X0Split89A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split89A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split89A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split89A3X0_pairs. -/
theorem X0Split89A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split89A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A0X0Y0Certs : List (Nat × Nat) := [
  (120, 0), (140, 715), (192, 0), (337, 106), (478, 1652),
  (492, 254), (678, 558), (780, 3), (834, 1097)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0X0Y0_check. -/
theorem X0Split90A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0X0Y0_pairs. -/
theorem X0Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0X0_pairs. -/
theorem X0Split90A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A0_pairs. -/
theorem X0Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A1X0Y0Certs : List (Nat × Nat) := [
  (44, 341), (105, 0), (219, 0), (306, 84), (709, 632),
  (873, 38)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1X0Y0_check. -/
theorem X0Split90A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1X0Y0_pairs. -/
theorem X0Split90A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split90A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1X0_pairs. -/
theorem X0Split90A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A1_pairs. -/
theorem X0Split90A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A2X0Y0Certs : List (Nat × Nat) := [
  (152, 20), (295, 1224), (321, 0), (523, 296), (638, 131)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2X0Y0_check. -/
theorem X0Split90A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2X0Y0_pairs. -/
theorem X0Split90A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split90A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2X0_pairs. -/
theorem X0Split90A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A2_pairs. -/
theorem X0Split90A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split90A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3X0Y0_check. -/
theorem X0Split90A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3X0Y0_pairs. -/
theorem X0Split90A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split90A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split90A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3X0_pairs. -/
theorem X0Split90A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split90A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split90A3_pairs. -/
theorem X0Split90A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split90A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0X0Y0_check. -/
theorem X0Split91A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0X0Y0_pairs. -/
theorem X0Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0X0_pairs. -/
theorem X0Split91A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A0_pairs. -/
theorem X0Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 6 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A1X0Y0Certs : List (Nat × Nat) := [
  (232, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1X0Y0_check. -/
theorem X0Split91A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1X0Y0_pairs. -/
theorem X0Split91A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1X0_pairs. -/
theorem X0Split91A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A1_pairs. -/
theorem X0Split91A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 6 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A2X0Y0Certs : List (Nat × Nat) := [
  (69, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2X0Y0_check. -/
theorem X0Split91A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2X0Y0_pairs. -/
theorem X0Split91A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2X0_pairs. -/
theorem X0Split91A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A2_pairs. -/
theorem X0Split91A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 6 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split91A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3X0Y0_check. -/
theorem X0Split91A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3X0Y0_pairs. -/
theorem X0Split91A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split91A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split91A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3X0_pairs. -/
theorem X0Split91A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split91A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split91A3_pairs. -/
theorem X0Split91A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 6 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split91A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0X0Y0_check. -/
theorem X0Split92A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0X0Y0_pairs. -/
theorem X0Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0X0_pairs. -/
theorem X0Split92A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A0_pairs. -/
theorem X0Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1X0Y0_check. -/
theorem X0Split92A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1X0Y0_pairs. -/
theorem X0Split92A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split92A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1X0_pairs. -/
theorem X0Split92A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A1_pairs. -/
theorem X0Split92A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2X0Y0_check. -/
theorem X0Split92A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2X0Y0_pairs. -/
theorem X0Split92A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split92A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2X0_pairs. -/
theorem X0Split92A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A2_pairs. -/
theorem X0Split92A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split92A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3X0Y0_check. -/
theorem X0Split92A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3X0Y0_pairs. -/
theorem X0Split92A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split92A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split92A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3X0_pairs. -/
theorem X0Split92A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split92A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split92A3_pairs. -/
theorem X0Split92A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split92A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0X0Y0_check. -/
theorem X0Split93A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0X0Y0_pairs. -/
theorem X0Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0X0_pairs. -/
theorem X0Split93A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A0_pairs. -/
theorem X0Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 7 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1X0Y0_check. -/
theorem X0Split93A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1X0Y0_pairs. -/
theorem X0Split93A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split93A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1X0_pairs. -/
theorem X0Split93A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A1_pairs. -/
theorem X0Split93A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 7 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2X0Y0_check. -/
theorem X0Split93A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2X0Y0_pairs. -/
theorem X0Split93A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split93A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2X0_pairs. -/
theorem X0Split93A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A2_pairs. -/
theorem X0Split93A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 7 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split93A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3X0Y0_check. -/
theorem X0Split93A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3X0Y0_pairs. -/
theorem X0Split93A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split93A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split93A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3X0_pairs. -/
theorem X0Split93A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split93A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split93A3_pairs. -/
theorem X0Split93A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 7 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split93A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0X0Y0_check. -/
theorem X0Split94A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0X0Y0_pairs. -/
theorem X0Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 8 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0X0_pairs. -/
theorem X0Split94A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 8 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A0_pairs. -/
theorem X0Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 8 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1X0Y0_check. -/
theorem X0Split94A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1X0Y0_pairs. -/
theorem X0Split94A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 8 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split94A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1X0_pairs. -/
theorem X0Split94A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 8 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A1_pairs. -/
theorem X0Split94A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 8 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2X0Y0_check. -/
theorem X0Split94A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2X0Y0_pairs. -/
theorem X0Split94A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 8 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split94A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2X0_pairs. -/
theorem X0Split94A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 8 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A2_pairs. -/
theorem X0Split94A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 8 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split94A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3X0Y0_check. -/
theorem X0Split94A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3X0Y0_pairs. -/
theorem X0Split94A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 8 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split94A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split94A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3X0_pairs. -/
theorem X0Split94A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 8 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split94A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split94A3_pairs. -/
theorem X0Split94A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 8 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split94A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

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
def X1Split80A0X0Y0Certs : List (Nat × Nat) := [
  (1428, 2921)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X0Y0_check. -/
theorem X1Split80A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X0Y0_pairs. -/
theorem X1Split80A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X0_pairs. -/
theorem X1Split80A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X1Y0_check. -/
theorem X1Split80A0X1Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X1Y0_pairs. -/
theorem X1Split80A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk1 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X1_pairs. -/
theorem X1Split80A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X2Y0Certs : List (Nat × Nat) := [
  (281, 3426), (746, 2969)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X2Y0_check. -/
theorem X1Split80A0X2Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X2Y0_pairs. -/
theorem X1Split80A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X2Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk2 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X2_pairs. -/
theorem X1Split80A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X3Y0Certs : List (Nat × Nat) := [
  (492, 1850)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X3Y0_check. -/
theorem X1Split80A0X3Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X3Y0_pairs. -/
theorem X1Split80A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X3Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk3 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X3_pairs. -/
theorem X1Split80A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X4Y0Certs : List (Nat × Nat) := [
  (404, 995)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X4Y0_check. -/
theorem X1Split80A0X4Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X4Y0_pairs. -/
theorem X1Split80A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X4Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk4 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X4_pairs. -/
theorem X1Split80A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X5Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X5Y0_check. -/
theorem X1Split80A0X5Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X5Y0_pairs. -/
theorem X1Split80A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X5Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk5 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X5_pairs. -/
theorem X1Split80A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X6Y0Certs : List (Nat × Nat) := [
  (757, 2914), (817, 1691)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X6Y0_check. -/
theorem X1Split80A0X6Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X6Y0_pairs. -/
theorem X1Split80A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X6Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk6 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X6_pairs. -/
theorem X1Split80A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X7Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X7Y0_check. -/
theorem X1Split80A0X7Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X7Y0_pairs. -/
theorem X1Split80A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X7Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk7 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X7_pairs. -/
theorem X1Split80A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X8Y0Certs : List (Nat × Nat) := [
  (393, 1330), (1184, 2433), (1439, 1238)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X8Y0_check. -/
theorem X1Split80A0X8Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X8Y0_pairs. -/
theorem X1Split80A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X8Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk8 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X8_pairs. -/
theorem X1Split80A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X9Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X9Y0_check. -/
theorem X1Split80A0X9Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X9Y0_pairs. -/
theorem X1Split80A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X9Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk9 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X9_pairs. -/
theorem X1Split80A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X10Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X10Y0_check. -/
theorem X1Split80A0X10Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X10Y0_pairs. -/
theorem X1Split80A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X10Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk10 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X10_pairs. -/
theorem X1Split80A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X11Y0_check. -/
theorem X1Split80A0X11Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X11Y0_pairs. -/
theorem X1Split80A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X11Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk11 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X11_pairs. -/
theorem X1Split80A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X12Y0Certs : List (Nat × Nat) := [
  (21, 2818), (1941, 895)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X12Y0_check. -/
theorem X1Split80A0X12Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X12Y0_pairs. -/
theorem X1Split80A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X12Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk12 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X12_pairs. -/
theorem X1Split80A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X13Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X13Y0_check. -/
theorem X1Split80A0X13Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X13Y0_pairs. -/
theorem X1Split80A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X13Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk13 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X13_pairs. -/
theorem X1Split80A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X14Y0Certs : List (Nat × Nat) := [
  (1235, 1463), (1367, 2250), (1528, 3131)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X14Y0_check. -/
theorem X1Split80A0X14Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X14Y0_pairs. -/
theorem X1Split80A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X14Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk14 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X14_pairs. -/
theorem X1Split80A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X15Y0Certs : List (Nat × Nat) := [
  (395, 2203)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X15Y0_check. -/
theorem X1Split80A0X15Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X15Y0_pairs. -/
theorem X1Split80A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X15Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk15 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X15_pairs. -/
theorem X1Split80A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X16Y0Certs : List (Nat × Nat) := [
  (237, 3490), (741, 2054)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X16Y0_check. -/
theorem X1Split80A0X16Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X16Y0_pairs. -/
theorem X1Split80A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X16Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk16 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X16_pairs. -/
theorem X1Split80A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split80A0X17Y0Certs : List (Nat × Nat) := [
  (958, 1364), (1154, 917)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X17Y0_check. -/
theorem X1Split80A0X17Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X17Y0_pairs. -/
theorem X1Split80A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split80A0X17Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk17 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split80A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0X17_pairs. -/
theorem X1Split80A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split80A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split80A0_pairs. -/
theorem X1Split80A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split80A0X0_pairs x hx y hy hw
  · exact X1Split80A0X1_pairs x hx y hy hw
  · exact X1Split80A0X2_pairs x hx y hy hw
  · exact X1Split80A0X3_pairs x hx y hy hw
  · exact X1Split80A0X4_pairs x hx y hy hw
  · exact X1Split80A0X5_pairs x hx y hy hw
  · exact X1Split80A0X6_pairs x hx y hy hw
  · exact X1Split80A0X7_pairs x hx y hy hw
  · exact X1Split80A0X8_pairs x hx y hy hw
  · exact X1Split80A0X9_pairs x hx y hy hw
  · exact X1Split80A0X10_pairs x hx y hy hw
  · exact X1Split80A0X11_pairs x hx y hy hw
  · exact X1Split80A0X12_pairs x hx y hy hw
  · exact X1Split80A0X13_pairs x hx y hy hw
  · exact X1Split80A0X14_pairs x hx y hy hw
  · exact X1Split80A0X15_pairs x hx y hy hw
  · exact X1Split80A0X16_pairs x hx y hy hw
  · exact X1Split80A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X0Y0Certs : List (Nat × Nat) := [
  (5673, 1834), (44213, 2018), (53077, 1001)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X0Y0_check. -/
theorem X1Split81A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X0Y0_pairs. -/
theorem X1Split81A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X0_pairs. -/
theorem X1Split81A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X1Y0Certs : List (Nat × Nat) := [
  (1833, 2936), (25715, 1365), (26629, 2471)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X1Y0_check. -/
theorem X1Split81A0X1Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X1Y0_pairs. -/
theorem X1Split81A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X1_pairs. -/
theorem X1Split81A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X2Y0Certs : List (Nat × Nat) := [
  (26916, 2913), (27138, 1833), (38796, 477), (49960, 552)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X2Y0_check. -/
theorem X1Split81A0X2Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X2Y0_pairs. -/
theorem X1Split81A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X2Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk2 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X2_pairs. -/
theorem X1Split81A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X3Y0Certs : List (Nat × Nat) := [
  (11795, 2378), (14613, 526), (16972, 2243), (32328, 522)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X3Y0_check. -/
theorem X1Split81A0X3Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X3Y0_pairs. -/
theorem X1Split81A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X3Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk3 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X3_pairs. -/
theorem X1Split81A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X4Y0Certs : List (Nat × Nat) := [
  (9752, 1803), (16227, 2609), (17807, 3042), (31469, 3240), (35186, 516),
  (37633, 1856)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X4Y0_check. -/
theorem X1Split81A0X4Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X4Y0_pairs. -/
theorem X1Split81A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X4Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk4 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X4_pairs. -/
theorem X1Split81A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X5Y0Certs : List (Nat × Nat) := [
  (11737, 1189), (12323, 2754), (35219, 2377)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X5Y0_check. -/
theorem X1Split81A0X5Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X5Y0_pairs. -/
theorem X1Split81A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X5Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk5 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X5_pairs. -/
theorem X1Split81A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X6Y0Certs : List (Nat × Nat) := [
  (30550, 2067), (32544, 2439)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X6Y0_check. -/
theorem X1Split81A0X6Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X6Y0_pairs. -/
theorem X1Split81A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X6Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk6 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X6_pairs. -/
theorem X1Split81A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X7Y0Certs : List (Nat × Nat) := [
  (2807, 1927), (12286, 1233), (13542, 868), (14400, 972), (29291, 1040),
  (42372, 1093)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X7Y0_check. -/
theorem X1Split81A0X7Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X7Y0_pairs. -/
theorem X1Split81A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X7Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk7 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X7_pairs. -/
theorem X1Split81A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X8Y0Certs : List (Nat × Nat) := [
  (12035, 1171), (33829, 2997), (35706, 2289), (37060, 1530), (40879, 3006),
  (41236, 3081), (42907, 1192), (43099, 1300), (47036, 3047), (47459, 1148),
  (47813, 2671)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X8Y0_check. -/
theorem X1Split81A0X8Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X8Y0_pairs. -/
theorem X1Split81A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X8Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk8 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X8_pairs. -/
theorem X1Split81A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X9Y0Certs : List (Nat × Nat) := [
  (6510, 1184)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X9Y0_check. -/
theorem X1Split81A0X9Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X9Y0_pairs. -/
theorem X1Split81A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X9Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk9 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X9_pairs. -/
theorem X1Split81A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X10Y0Certs : List (Nat × Nat) := [
  (5713, 1483), (36913, 2180), (37082, 2456), (37947, 3242), (41786, 617),
  (49170, 1478)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X10Y0_check. -/
theorem X1Split81A0X10Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X10Y0_pairs. -/
theorem X1Split81A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X10Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk10 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X10_pairs. -/
theorem X1Split81A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X11Y0Certs : List (Nat × Nat) := [
  (11321, 1506)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X11Y0_check. -/
theorem X1Split81A0X11Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X11Y0_pairs. -/
theorem X1Split81A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X11Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk11 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X11_pairs. -/
theorem X1Split81A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X12Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X12Y0_check. -/
theorem X1Split81A0X12Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X12Y0_pairs. -/
theorem X1Split81A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X12Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk12 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X12_pairs. -/
theorem X1Split81A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X13Y0Certs : List (Nat × Nat) := [
  (3886, 2947), (6783, 266)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X13Y0_check. -/
theorem X1Split81A0X13Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X13Y0_pairs. -/
theorem X1Split81A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X13Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk13 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X13_pairs. -/
theorem X1Split81A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X14Y0Certs : List (Nat × Nat) := [
  (8702, 2168), (12054, 180), (16432, 3008), (37393, 2183), (37480, 2146),
  (37967, 2502), (40134, 986), (42896, 1435), (50058, 923)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X14Y0_check. -/
theorem X1Split81A0X14Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X14Y0_pairs. -/
theorem X1Split81A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X14Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk14 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X14_pairs. -/
theorem X1Split81A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X15Y0Certs : List (Nat × Nat) := [
  (1374, 2061), (11692, 2960), (12192, 397), (14266, 2548), (19985, 193),
  (20741, 2117), (21327, 3359)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X15Y0_check. -/
theorem X1Split81A0X15Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X15Y0_pairs. -/
theorem X1Split81A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X15Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk15 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X15_pairs. -/
theorem X1Split81A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X16Y0Certs : List (Nat × Nat) := [
  (46327, 677), (49462, 1286)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X16Y0_check. -/
theorem X1Split81A0X16Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X16Y0_pairs. -/
theorem X1Split81A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X16Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk16 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X16_pairs. -/
theorem X1Split81A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split81A0X17Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X17Y0_check. -/
theorem X1Split81A0X17Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X17Y0_pairs. -/
theorem X1Split81A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split81A0X17Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks4S2048Chunk17 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X1M1Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split81A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0X17_pairs. -/
theorem X1Split81A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split81A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split81A0_pairs. -/
theorem X1Split81A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split81A0X0_pairs x hx y hy hw
  · exact X1Split81A0X1_pairs x hx y hy hw
  · exact X1Split81A0X2_pairs x hx y hy hw
  · exact X1Split81A0X3_pairs x hx y hy hw
  · exact X1Split81A0X4_pairs x hx y hy hw
  · exact X1Split81A0X5_pairs x hx y hy hw
  · exact X1Split81A0X6_pairs x hx y hy hw
  · exact X1Split81A0X7_pairs x hx y hy hw
  · exact X1Split81A0X8_pairs x hx y hy hw
  · exact X1Split81A0X9_pairs x hx y hy hw
  · exact X1Split81A0X10_pairs x hx y hy hw
  · exact X1Split81A0X11_pairs x hx y hy hw
  · exact X1Split81A0X12_pairs x hx y hy hw
  · exact X1Split81A0X13_pairs x hx y hy hw
  · exact X1Split81A0X14_pairs x hx y hy hw
  · exact X1Split81A0X15_pairs x hx y hy hw
  · exact X1Split81A0X16_pairs x hx y hy hw
  · exact X1Split81A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X0Y0_check. -/
theorem X1Split82A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X0Y0_pairs. -/
theorem X1Split82A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A0X1Y0Certs : List (Nat × Nat) := [
  (2662, 273), (6100, 89), (7204, 0), (7591, 0), (7715, 2140),
  (8444, 990), (8634, 0), (8642, 0), (8751, 269), (8868, 0),
  (9010, 0), (9129, 3368), (9975, 3148), (11880, 713), (13511, 0),
  (15379, 845), (16615, 0), (17941, 0), (18040, 0), (18996, 1853),
  (19308, 912), (22968, 0), (23573, 0), (24283, 2605), (24311, 2892),
  (24399, 0), (24698, 2323), (25079, 1805), (26190, 0), (26745, 0),
  (26828, 1887), (26855, 2141), (27908, 367), (29814, 1408), (30386, 2741),
  (30578, 0), (31236, 0), (33889, 0), (35585, 2543), (36869, 2277),
  (37723, 2085), (38140, 0), (38241, 2971), (40207, 0), (44395, 0),
  (44677, 0), (46176, 364), (47983, 692), (48550, 0), (48795, 0),
  (49335, 0), (51377, 256), (51787, 0), (52705, 0), (52937, 0),
  (53038, 3073), (53637, 686), (53867, 2623), (55142, 2292), (55162, 0),
  (55736, 309), (57442, 143), (59403, 1442), (59538, 0), (60884, 3235),
  (61076, 977), (61429, 498), (61861, 0), (63094, 0), (63331, 1582),
  (63478, 3074), (64068, 0), (64306, 0), (64768, 0), (65450, 0),
  (66116, 3421), (66355, 0), (68053, 1115), (68832, 538), (71854, 0),
  (72098, 0), (72156, 0), (72800, 850), (72812, 0), (74880, 0),
  (74997, 0), (76594, 0), (76950, 0), (77176, 0), (77556, 656),
  (77746, 0), (78457, 0), (78686, 2893), (78984, 1508)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X1Y0_check. -/
theorem X1Split82A0X1Y0_check : checkGrid m4TX1 censusX1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A0X1Y0_pairs. -/
theorem X1Split82A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A1X0Y0Certs : List (Nat × Nat) := [
  (3619, 744), (14744, 2908), (14773, 0), (19690, 596), (28482, 1213),
  (47529, 592), (52769, 701), (71942, 0), (73197, 0), (86312, 1015),
  (104712, 2080), (104782, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X0Y0_check. -/
theorem X1Split82A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X0Y0_pairs. -/
theorem X1Split82A1X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A1X1Y0Certs : List (Nat × Nat) := [
  (21963, 1258), (25039, 0), (34931, 0), (39414, 0), (54067, 0),
  (54354, 3201), (58200, 0), (60564, 514), (64539, 859), (66516, 0),
  (72813, 0), (74635, 1516), (78810, 0), (79158, 3262)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X1Y0_check. -/
theorem X1Split82A1X1Y0_check : checkGrid m4TX1 censusX1 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A1X1Y0_pairs. -/
theorem X1Split82A1X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A1X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X0Y0_check. -/
theorem X1Split82A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X0Y0_pairs. -/
theorem X1Split82A2X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A2X1Y0Certs : List (Nat × Nat) := [
  (4882, 0), (8791, 0), (19514, 0), (22019, 0), (26727, 0),
  (31312, 3338), (32954, 0), (53360, 1841), (55737, 0), (71439, 515)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X1Y0_check. -/
theorem X1Split82A2X1Y0_check : checkGrid m4TX1 censusX1 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A2X1Y0_pairs. -/
theorem X1Split82A2X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A2X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A3X0Y0Certs : List (Nat × Nat) := [
  (27730, 2267)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X0Y0_check. -/
theorem X1Split82A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X0Y0_pairs. -/
theorem X1Split82A3X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split82A3X1Y0Certs : List (Nat × Nat) := [
  (31524, 0), (59327, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X1Y0_check. -/
theorem X1Split82A3X1Y0_check : checkGrid m4TX1 censusX1 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split82A3X1Y0_pairs. -/
theorem X1Split82A3X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split82A3X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X0Y0Certs : List (Nat × Nat) := [
  (29936, 2259)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X0Y0_check. -/
theorem X1Split83A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X0Y0_pairs. -/
theorem X1Split83A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X0_pairs. -/
theorem X1Split83A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X1Y0Certs : List (Nat × Nat) := [
  (8450, 1104), (13822, 1396), (24775, 2026), (25141, 17)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X1Y0_check. -/
theorem X1Split83A0X1Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X1Y0_pairs. -/
theorem X1Split83A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X1_pairs. -/
theorem X1Split83A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X2Y0Certs : List (Nat × Nat) := [
  (5570, 1108), (21389, 3167), (49390, 241), (53435, 80)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X2Y0_check. -/
theorem X1Split83A0X2Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X2Y0_pairs. -/
theorem X1Split83A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk2 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X2Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk2 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X2_pairs. -/
theorem X1Split83A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X3Y0Certs : List (Nat × Nat) := [
  (5520, 5), (16434, 1768), (33813, 49)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X3Y0_check. -/
theorem X1Split83A0X3Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X3Y0_pairs. -/
theorem X1Split83A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk3 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X3Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk3 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X3_pairs. -/
theorem X1Split83A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X4Y0Certs : List (Nat × Nat) := [
  (12259, 956), (22906, 631), (37600, 242)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X4Y0_check. -/
theorem X1Split83A0X4Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X4Y0_pairs. -/
theorem X1Split83A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk4 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X4Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk4 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X4_pairs. -/
theorem X1Split83A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X5Y0Certs : List (Nat × Nat) := [
  (2509, 960), (28945, 2035), (40736, 2264)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X5Y0_check. -/
theorem X1Split83A0X5Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X5Y0_pairs. -/
theorem X1Split83A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk5 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X5Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk5 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X5_pairs. -/
theorem X1Split83A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X6Y0Certs : List (Nat × Nat) := [
  (12011, 296), (25999, 959), (28168, 2851), (28774, 57), (30472, 1391),
  (31381, 12)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X6Y0_check. -/
theorem X1Split83A0X6Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X6Y0_pairs. -/
theorem X1Split83A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk6 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X6Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk6 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X6_pairs. -/
theorem X1Split83A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X7Y0Certs : List (Nat × Nat) := [
  (4696, 633), (58270, 244)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X7Y0_check. -/
theorem X1Split83A0X7Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X7Y0_pairs. -/
theorem X1Split83A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk7 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X7Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk7 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X7_pairs. -/
theorem X1Split83A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X8Y0Certs : List (Nat × Nat) := [
  (3506, 2263), (22652, 30), (22909, 958), (42676, 634), (45723, 41)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X8Y0_check. -/
theorem X1Split83A0X8Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X8Y0_pairs. -/
theorem X1Split83A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk8 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X8Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk8 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X8_pairs. -/
theorem X1Split83A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X9Y0Certs : List (Nat × Nat) := [
  (1357, 129)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X9Y0_check. -/
theorem X1Split83A0X9Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X9Y0_pairs. -/
theorem X1Split83A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk9 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X9Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk9 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X9_pairs. -/
theorem X1Split83A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X10Y0Certs : List (Nat × Nat) := [
  (10595, 86), (13644, 1773), (15520, 239), (22543, 422), (36073, 415),
  (48037, 135), (57748, 2853)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X10Y0_check. -/
theorem X1Split83A0X10Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X10Y0_pairs. -/
theorem X1Split83A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk10 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X10Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk10 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X10_pairs. -/
theorem X1Split83A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X11Y0_check. -/
theorem X1Split83A0X11Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X11Y0_pairs. -/
theorem X1Split83A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk11 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X11Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk11 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X11_pairs. -/
theorem X1Split83A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X12Y0Certs : List (Nat × Nat) := [
  (338, 170), (5655, 557), (18174, 1772), (37427, 728), (40752, 351),
  (46658, 164), (55479, 198)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X12Y0_check. -/
theorem X1Split83A0X12Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X12Y0_pairs. -/
theorem X1Split83A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk12 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X12Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk12 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X12_pairs. -/
theorem X1Split83A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X13Y0Certs : List (Nat × Nat) := [
  (166, 636), (3746, 2260), (3843, 48), (5104, 61)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X13Y0_check. -/
theorem X1Split83A0X13Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X13Y0_pairs. -/
theorem X1Split83A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk13 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X13Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk13 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X13_pairs. -/
theorem X1Split83A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X14Y0Certs : List (Nat × Nat) := [
  (8307, 2574), (14623, 424), (16655, 85), (16963, 416), (34432, 1395),
  (58176, 103), (58584, 1771)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X14Y0_check. -/
theorem X1Split83A0X14Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X14Y0_pairs. -/
theorem X1Split83A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk14 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X14Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk14 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X14_pairs. -/
theorem X1Split83A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X15Y0Certs : List (Nat × Nat) := [
  (9397, 136)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X15Y0_check. -/
theorem X1Split83A0X15Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X15Y0_pairs. -/
theorem X1Split83A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk15 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X15Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk15 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X15_pairs. -/
theorem X1Split83A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X16Y0Certs : List (Nat × Nat) := [
  (1612, 1390), (4124, 484), (10998, 831), (22941, 1240), (47375, 82),
  (49027, 128), (49863, 47), (53229, 204)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X16Y0_check. -/
theorem X1Split83A0X16Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X16Y0_pairs. -/
theorem X1Split83A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk16 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X16Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk16 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X16_pairs. -/
theorem X1Split83A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split83A0X17Y0Certs : List (Nat × Nat) := [
  (1851, 1242), (14783, 1567), (19334, 487), (32235, 559)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X17Y0_check. -/
theorem X1Split83A0X17Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X17Y0_pairs. -/
theorem X1Split83A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks4S2048Chunk17 masks1S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split83A0X17Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk17 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split83A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0X17_pairs. -/
theorem X1Split83A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split83A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split83A0_pairs. -/
theorem X1Split83A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split83A0X0_pairs x hx y hy hw
  · exact X1Split83A0X1_pairs x hx y hy hw
  · exact X1Split83A0X2_pairs x hx y hy hw
  · exact X1Split83A0X3_pairs x hx y hy hw
  · exact X1Split83A0X4_pairs x hx y hy hw
  · exact X1Split83A0X5_pairs x hx y hy hw
  · exact X1Split83A0X6_pairs x hx y hy hw
  · exact X1Split83A0X7_pairs x hx y hy hw
  · exact X1Split83A0X8_pairs x hx y hy hw
  · exact X1Split83A0X9_pairs x hx y hy hw
  · exact X1Split83A0X10_pairs x hx y hy hw
  · exact X1Split83A0X11_pairs x hx y hy hw
  · exact X1Split83A0X12_pairs x hx y hy hw
  · exact X1Split83A0X13_pairs x hx y hy hw
  · exact X1Split83A0X14_pairs x hx y hy hw
  · exact X1Split83A0X15_pairs x hx y hy hw
  · exact X1Split83A0X16_pairs x hx y hy hw
  · exact X1Split83A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X0Y0_check. -/
theorem X1Split84A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X0Y0_pairs. -/
theorem X1Split84A0X0Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk0_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X0_pairs. -/
theorem X1Split84A0X0_pairs : ∀ x ∈ outerMasks4S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X1Y0_check. -/
theorem X1Split84A0X1Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X1Y0_pairs. -/
theorem X1Split84A0X1Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk1 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk1 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk1_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X1_pairs. -/
theorem X1Split84A0X1_pairs : ∀ x ∈ outerMasks4S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X2Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X2Y0_check. -/
theorem X1Split84A0X2Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X2Y0_pairs. -/
theorem X1Split84A0X2Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk2 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk2 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X2Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk2_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk2 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk2_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk2_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X2_pairs. -/
theorem X1Split84A0X2_pairs : ∀ x ∈ outerMasks4S2048Chunk2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X3Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X3Y0_check. -/
theorem X1Split84A0X3Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X3Y0_pairs. -/
theorem X1Split84A0X3Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk3 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk3 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X3Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk3_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk3 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk3_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk3_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X3_pairs. -/
theorem X1Split84A0X3_pairs : ∀ x ∈ outerMasks4S2048Chunk3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X4Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X4Y0_check. -/
theorem X1Split84A0X4Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X4Y0_pairs. -/
theorem X1Split84A0X4Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk4 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk4 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X4Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk4_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk4 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk4_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk4_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X4_pairs. -/
theorem X1Split84A0X4_pairs : ∀ x ∈ outerMasks4S2048Chunk4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X5Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X5Y0_check. -/
theorem X1Split84A0X5Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X5Y0_pairs. -/
theorem X1Split84A0X5Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk5 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk5 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X5Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk5_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk5 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk5_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk5_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X5_pairs. -/
theorem X1Split84A0X5_pairs : ∀ x ∈ outerMasks4S2048Chunk5, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X6Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X6Y0_check. -/
theorem X1Split84A0X6Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X6Y0_pairs. -/
theorem X1Split84A0X6Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk6 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk6 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X6Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk6_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk6 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk6_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk6_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X6_pairs. -/
theorem X1Split84A0X6_pairs : ∀ x ∈ outerMasks4S2048Chunk6, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X7Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X7Y0_check. -/
theorem X1Split84A0X7Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X7Y0_pairs. -/
theorem X1Split84A0X7Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk7 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk7 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X7Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk7_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk7 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk7_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk7_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X7_pairs. -/
theorem X1Split84A0X7_pairs : ∀ x ∈ outerMasks4S2048Chunk7, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X8Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X8Y0_check. -/
theorem X1Split84A0X8Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X8Y0_pairs. -/
theorem X1Split84A0X8Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk8 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk8 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X8Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk8_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk8 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk8_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk8_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X8_pairs. -/
theorem X1Split84A0X8_pairs : ∀ x ∈ outerMasks4S2048Chunk8, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X9Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X9Y0_check. -/
theorem X1Split84A0X9Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X9Y0_pairs. -/
theorem X1Split84A0X9Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk9 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk9 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X9Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk9_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk9 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk9_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk9_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X9_pairs. -/
theorem X1Split84A0X9_pairs : ∀ x ∈ outerMasks4S2048Chunk9, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X10Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X10Y0_check. -/
theorem X1Split84A0X10Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X10Y0_pairs. -/
theorem X1Split84A0X10Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk10 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk10 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X10Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk10_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk10 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk10_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk10_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X10_pairs. -/
theorem X1Split84A0X10_pairs : ∀ x ∈ outerMasks4S2048Chunk10, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X11Y0_check. -/
theorem X1Split84A0X11Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X11Y0_pairs. -/
theorem X1Split84A0X11Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk11 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk11 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X11Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk11_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk11 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk11_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk11_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X11_pairs. -/
theorem X1Split84A0X11_pairs : ∀ x ∈ outerMasks4S2048Chunk11, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X12Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X12Y0_check. -/
theorem X1Split84A0X12Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X12Y0_pairs. -/
theorem X1Split84A0X12Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk12 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk12 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X12Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk12_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk12 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk12_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk12_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X12_pairs. -/
theorem X1Split84A0X12_pairs : ∀ x ∈ outerMasks4S2048Chunk12, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X13Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X13Y0_check. -/
theorem X1Split84A0X13Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X13Y0_pairs. -/
theorem X1Split84A0X13Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk13 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk13 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X13Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk13_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk13 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk13_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk13_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X13_pairs. -/
theorem X1Split84A0X13_pairs : ∀ x ∈ outerMasks4S2048Chunk13, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X14Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X14Y0_check. -/
theorem X1Split84A0X14Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X14Y0_pairs. -/
theorem X1Split84A0X14Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk14 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk14 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X14Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk14_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk14 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk14_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk14_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X14_pairs. -/
theorem X1Split84A0X14_pairs : ∀ x ∈ outerMasks4S2048Chunk14, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X15Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X15Y0_check. -/
theorem X1Split84A0X15Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X15Y0_pairs. -/
theorem X1Split84A0X15Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk15 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk15 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X15Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk15_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk15 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk15_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk15_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X15_pairs. -/
theorem X1Split84A0X15_pairs : ∀ x ∈ outerMasks4S2048Chunk15, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X16Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X16Y0_check. -/
theorem X1Split84A0X16Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X16Y0_pairs. -/
theorem X1Split84A0X16Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk16 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk16 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X16Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk16_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk16 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk16_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk16_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X16_pairs. -/
theorem X1Split84A0X16_pairs : ∀ x ∈ outerMasks4S2048Chunk16, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split84A0X17Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X17Y0_check. -/
theorem X1Split84A0X17Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X17Y0_pairs. -/
theorem X1Split84A0X17Y0_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks4S2048Chunk17 masks0S512Chunk0
    (gridWords outerMasks4S2048Chunk17 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split84A0X17Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks4S2048Chunk17_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks4S2048Chunk17 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks4S2048Chunk17_bound
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
      exact X1M0Left_bound x (outerMasks4S2048Chunk17_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split84A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0X17_pairs. -/
theorem X1Split84A0X17_pairs : ∀ x ∈ outerMasks4S2048Chunk17, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split84A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split84A0_pairs. -/
theorem X1Split84A0_pairs : ∀ x ∈ masksOfWt 30 4, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks4S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split84A0X0_pairs x hx y hy hw
  · exact X1Split84A0X1_pairs x hx y hy hw
  · exact X1Split84A0X2_pairs x hx y hy hw
  · exact X1Split84A0X3_pairs x hx y hy hw
  · exact X1Split84A0X4_pairs x hx y hy hw
  · exact X1Split84A0X5_pairs x hx y hy hw
  · exact X1Split84A0X6_pairs x hx y hy hw
  · exact X1Split84A0X7_pairs x hx y hy hw
  · exact X1Split84A0X8_pairs x hx y hy hw
  · exact X1Split84A0X9_pairs x hx y hy hw
  · exact X1Split84A0X10_pairs x hx y hy hw
  · exact X1Split84A0X11_pairs x hx y hy hw
  · exact X1Split84A0X12_pairs x hx y hy hw
  · exact X1Split84A0X13_pairs x hx y hy hw
  · exact X1Split84A0X14_pairs x hx y hy hw
  · exact X1Split84A0X15_pairs x hx y hy hw
  · exact X1Split84A0X16_pairs x hx y hy hw
  · exact X1Split84A0X17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A0X0Y0Certs : List (Nat × Nat) := [
  (277, 0), (541, 0), (1822, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0Y0_check. -/
theorem X1Split85A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0Y0_pairs. -/
theorem X1Split85A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split85A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A0X0Y1Certs : List (Nat × Nat) := [
  (20, 0), (388, 0), (1392, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0Y1_check. -/
theorem X1Split85A0X0Y1_check : checkGrid m4TX1 censusX1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0Y1_pairs. -/
theorem X1Split85A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A0X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split85A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A0X0_pairs. -/
theorem X1Split85A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split85A0X0Y0_pairs x hx y hy hw
  · exact X1Split85A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0Y0_check. -/
theorem X1Split85A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0Y0_pairs. -/
theorem X1Split85A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split85A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A1X0Y1Certs : List (Nat × Nat) := [
  (1749, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0Y1_check. -/
theorem X1Split85A1X0Y1_check : checkGrid m4TX1 censusX1 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A1X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0Y1_pairs. -/
theorem X1Split85A1X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A1X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split85A1X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A1X0_pairs. -/
theorem X1Split85A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split85A1X0Y0_pairs x hx y hy hw
  · exact X1Split85A1X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A2X0Y0Certs : List (Nat × Nat) := [
  (333, 0), (1124, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0Y0_check. -/
theorem X1Split85A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0Y0_pairs. -/
theorem X1Split85A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split85A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A2X0Y1Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0Y1_check. -/
theorem X1Split85A2X0Y1_check : checkGrid m4TX1 censusX1 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A2X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0Y1_pairs. -/
theorem X1Split85A2X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A2X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split85A2X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A2X0_pairs. -/
theorem X1Split85A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split85A2X0Y0_pairs x hx y hy hw
  · exact X1Split85A2X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A3X0Y0Certs : List (Nat × Nat) := [
  (88, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0Y0_check. -/
theorem X1Split85A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0Y0_pairs. -/
theorem X1Split85A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split85A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split85A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split85A3X0Y1Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0Y1_check. -/
theorem X1Split85A3X0Y1_check : checkGrid m4TX1 censusX1 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A3X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0Y1_pairs. -/
theorem X1Split85A3X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns) X1Split85A3X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split85A3X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split85A3X0_pairs. -/
theorem X1Split85A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split85A3X0Y0_pairs x hx y hy hw
  · exact X1Split85A3X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A0X0Y0Certs : List (Nat × Nat) := [
  (1139, 0), (1161, 1851), (1921, 0), (2823, 1256), (2967, 0),
  (3124, 0), (3248, 0), (5242, 141), (6706, 0), (7111, 0),
  (7221, 0), (7745, 2542), (7912, 434), (10388, 2880), (11798, 280),
  (12230, 0), (12700, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A0X0Y0_check. -/
theorem X1Split86A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A0X0Y0_pairs. -/
theorem X1Split86A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split86A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A0X0_pairs. -/
theorem X1Split86A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A1X0Y0Certs : List (Nat × Nat) := [
  (180, 996), (5036, 1526), (8933, 0), (11517, 0), (11837, 0),
  (11986, 0), (12749, 704)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A1X0Y0_check. -/
theorem X1Split86A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A1X0Y0_pairs. -/
theorem X1Split86A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split86A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A1X0_pairs. -/
theorem X1Split86A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A2X0Y0Certs : List (Nat × Nat) := [
  (935, 0), (2449, 0), (5840, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A2X0Y0_check. -/
theorem X1Split86A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A2X0Y0_pairs. -/
theorem X1Split86A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split86A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A2X0_pairs. -/
theorem X1Split86A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split86A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A3X0Y0_check. -/
theorem X1Split86A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A3X0Y0_pairs. -/
theorem X1Split86A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split86A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split86A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split86A3X0_pairs. -/
theorem X1Split86A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split86A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0X0Y0_check. -/
theorem X1Split87A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0X0Y0_pairs. -/
theorem X1Split87A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0X0_pairs. -/
theorem X1Split87A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A0_pairs. -/
theorem X1Split87A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split87A1X0Y0Certs : List (Nat × Nat) := [
  (633, 39), (1002, 350), (1955, 78), (9272, 0), (11318, 0),
  (11599, 0), (12356, 2265), (12579, 0), (12623, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1X0Y0_check. -/
theorem X1Split87A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1X0Y0_pairs. -/
theorem X1Split87A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1X0_pairs. -/
theorem X1Split87A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A1_pairs. -/
theorem X1Split87A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split87A2X0Y0Certs : List (Nat × Nat) := [
  (84, 0), (779, 3159), (1728, 0), (2977, 0), (4617, 0),
  (6110, 0), (6180, 3), (6503, 0), (8111, 0), (9447, 0),
  (9527, 0), (9661, 0), (11873, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2X0Y0_check. -/
theorem X1Split87A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2X0Y0_pairs. -/
theorem X1Split87A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2X0_pairs. -/
theorem X1Split87A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A2_pairs. -/
theorem X1Split87A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split87A3X0Y0Certs : List (Nat × Nat) := [
  (9022, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3X0Y0_check. -/
theorem X1Split87A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3X0Y0_pairs. -/
theorem X1Split87A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split87A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split87A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3X0_pairs. -/
theorem X1Split87A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split87A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split87A3_pairs. -/
theorem X1Split87A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split87A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A0X0Y0Certs : List (Nat × Nat) := [
  (180, 0), (1982, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X0Y0_check. -/
theorem X1Split88A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X0Y0_pairs. -/
theorem X1Split88A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X0_pairs. -/
theorem X1Split88A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A0X1Y0Certs : List (Nat × Nat) := [
  (574, 0), (1123, 0), (1715, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X1Y0_check. -/
theorem X1Split88A0X1Y0_check : checkGrid m4TX1 censusX1 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X1Y0_pairs. -/
theorem X1Split88A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0X1_pairs. -/
theorem X1Split88A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A0_pairs. -/
theorem X1Split88A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split88A0X0_pairs x hx y hy hw
  · exact X1Split88A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X0Y0_check. -/
theorem X1Split88A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X0Y0_pairs. -/
theorem X1Split88A1X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X0_pairs. -/
theorem X1Split88A1X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A1X1Y0Certs : List (Nat × Nat) := [
  (1292, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X1Y0_check. -/
theorem X1Split88A1X1Y0_check : checkGrid m4TX1 censusX1 2 91076351 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X1Y0_pairs. -/
theorem X1Split88A1X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A1X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1X1_pairs. -/
theorem X1Split88A1X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A1_pairs. -/
theorem X1Split88A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split88A1X0_pairs x hx y hy hw
  · exact X1Split88A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A2X0Y0Certs : List (Nat × Nat) := [
  (593, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X0Y0_check. -/
theorem X1Split88A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X0Y0_pairs. -/
theorem X1Split88A2X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X0_pairs. -/
theorem X1Split88A2X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A2X1Y0Certs : List (Nat × Nat) := [
  (193, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X1Y0_check. -/
theorem X1Split88A2X1Y0_check : checkGrid m4TX1 censusX1 2 985062231 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X1Y0_pairs. -/
theorem X1Split88A2X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A2X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2X1_pairs. -/
theorem X1Split88A2X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A2_pairs. -/
theorem X1Split88A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split88A2X0_pairs x hx y hy hw
  · exact X1Split88A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X0Y0_check. -/
theorem X1Split88A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X0Y0_pairs. -/
theorem X1Split88A3X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X0_pairs. -/
theorem X1Split88A3X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split88A3X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X1Y0_check. -/
theorem X1Split88A3X1Y0_check : checkGrid m4TX1 censusX1 2 1071345064 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X1Y0_pairs. -/
theorem X1Split88A3X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split88A3X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact X1M2Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split88A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3X1_pairs. -/
theorem X1Split88A3X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split88A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split88A3_pairs. -/
theorem X1Split88A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split88A3X0_pairs x hx y hy hw
  · exact X1Split88A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A0X0Y0Certs : List (Nat × Nat) := [
  (44, 229), (191, 1110), (224, 1303), (230, 1361), (301, 2037),
  (304, 2045), (382, 2873)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A0X0Y0_check. -/
theorem X1Split89A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A0X0Y0_pairs. -/
theorem X1Split89A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split89A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A0X0_pairs. -/
theorem X1Split89A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A1X0Y0Certs : List (Nat × Nat) := [
  (113, 583), (119, 613)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A1X0Y0_check. -/
theorem X1Split89A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A1X0Y0_pairs. -/
theorem X1Split89A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split89A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A1X0_pairs. -/
theorem X1Split89A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A2X0Y0Certs : List (Nat × Nat) := [
  (387, 2896)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A2X0Y0_check. -/
theorem X1Split89A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A2X0Y0_pairs. -/
theorem X1Split89A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split89A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A2X0_pairs. -/
theorem X1Split89A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split89A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A3X0Y0_check. -/
theorem X1Split89A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A3X0Y0_pairs. -/
theorem X1Split89A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split89A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split89A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split89A3X0_pairs. -/
theorem X1Split89A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split89A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A0X0Y0Certs : List (Nat × Nat) := [
  (81, 0), (388, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0X0Y0_check. -/
theorem X1Split90A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0X0Y0_pairs. -/
theorem X1Split90A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split90A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0X0_pairs. -/
theorem X1Split90A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A0_pairs. -/
theorem X1Split90A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A1X0Y0Certs : List (Nat × Nat) := [
  (785, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1X0Y0_check. -/
theorem X1Split90A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1X0Y0_pairs. -/
theorem X1Split90A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split90A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1X0_pairs. -/
theorem X1Split90A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A1_pairs. -/
theorem X1Split90A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2X0Y0_check. -/
theorem X1Split90A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2X0Y0_pairs. -/
theorem X1Split90A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split90A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2X0_pairs. -/
theorem X1Split90A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A2_pairs. -/
theorem X1Split90A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split90A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3X0Y0_check. -/
theorem X1Split90A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3X0Y0_pairs. -/
theorem X1Split90A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split90A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M2Left_eq
    · exact X1M2Right_eq
    · intro x hx
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split90A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3X0_pairs. -/
theorem X1Split90A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split90A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split90A3_pairs. -/
theorem X1Split90A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split90A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0X0Y0_check. -/
theorem X1Split91A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0X0Y0_pairs. -/
theorem X1Split91A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0X0_pairs. -/
theorem X1Split91A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A0_pairs. -/
theorem X1Split91A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A1X0Y0Certs : List (Nat × Nat) := [
  (232, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1X0Y0_check. -/
theorem X1Split91A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1X0Y0_pairs. -/
theorem X1Split91A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1X0_pairs. -/
theorem X1Split91A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A1_pairs. -/
theorem X1Split91A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A2X0Y0Certs : List (Nat × Nat) := [
  (69, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2X0Y0_check. -/
theorem X1Split91A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2X0Y0_pairs. -/
theorem X1Split91A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2X0_pairs. -/
theorem X1Split91A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A2_pairs. -/
theorem X1Split91A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split91A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3X0Y0_check. -/
theorem X1Split91A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3X0Y0_pairs. -/
theorem X1Split91A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split91A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split91A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3X0_pairs. -/
theorem X1Split91A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split91A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split91A3_pairs. -/
theorem X1Split91A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split91A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0X0Y0_check. -/
theorem X1Split92A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0X0Y0_pairs. -/
theorem X1Split92A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split92A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0X0_pairs. -/
theorem X1Split92A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A0_pairs. -/
theorem X1Split92A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1X0Y0_check. -/
theorem X1Split92A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1X0Y0_pairs. -/
theorem X1Split92A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split92A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1X0_pairs. -/
theorem X1Split92A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A1_pairs. -/
theorem X1Split92A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2X0Y0_check. -/
theorem X1Split92A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2X0Y0_pairs. -/
theorem X1Split92A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split92A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2X0_pairs. -/
theorem X1Split92A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A2_pairs. -/
theorem X1Split92A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split92A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3X0Y0_check. -/
theorem X1Split92A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3X0Y0_pairs. -/
theorem X1Split92A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split92A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
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
      exact X1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split92A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3X0_pairs. -/
theorem X1Split92A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split92A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split92A3_pairs. -/
theorem X1Split92A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split92A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0X0Y0_check. -/
theorem X1Split93A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0X0Y0_pairs. -/
theorem X1Split93A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split93A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0X0_pairs. -/
theorem X1Split93A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A0_pairs. -/
theorem X1Split93A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 7 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1X0Y0_check. -/
theorem X1Split93A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1X0Y0_pairs. -/
theorem X1Split93A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A1X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split93A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1X0_pairs. -/
theorem X1Split93A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A1_pairs. -/
theorem X1Split93A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 7 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2X0Y0_check. -/
theorem X1Split93A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2X0Y0_pairs. -/
theorem X1Split93A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A2X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split93A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2X0_pairs. -/
theorem X1Split93A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A2_pairs. -/
theorem X1Split93A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 7 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split93A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3X0Y0_check. -/
theorem X1Split93A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3X0Y0_pairs. -/
theorem X1Split93A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split93A3X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact X1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split93A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3X0_pairs. -/
theorem X1Split93A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split93A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split93A3_pairs. -/
theorem X1Split93A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 7 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split93A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0X0Y0_check. -/
theorem X1Split94A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0X0Y0_pairs. -/
theorem X1Split94A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 8 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A0X0Y0Certs
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
  · exact X1Split94A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0X0_pairs. -/
theorem X1Split94A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 8 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A0_pairs. -/
theorem X1Split94A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 8 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1X0Y0_check. -/
theorem X1Split94A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1X0Y0_pairs. -/
theorem X1Split94A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 8 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A1X0Y0Certs
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
  · exact X1Split94A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1X0_pairs. -/
theorem X1Split94A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 8 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A1_pairs. -/
theorem X1Split94A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 8 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2X0Y0_check. -/
theorem X1Split94A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2X0Y0_pairs. -/
theorem X1Split94A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 8 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A2X0Y0Certs
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
  · exact X1Split94A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2X0_pairs. -/
theorem X1Split94A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 8 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A2_pairs. -/
theorem X1Split94A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 8 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split94A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3X0Y0_check. -/
theorem X1Split94A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3X0Y0_pairs. -/
theorem X1Split94A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 8 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split94A3X0Y0Certs
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
  · exact X1Split94A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3X0_pairs. -/
theorem X1Split94A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 8 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split94A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split94A3_pairs. -/
theorem X1Split94A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 8 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split94A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

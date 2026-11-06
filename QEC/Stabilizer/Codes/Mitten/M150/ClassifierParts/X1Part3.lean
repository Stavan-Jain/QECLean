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
def X1Split48A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0X0Y0_check. -/
theorem X1Split48A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0X0Y0_pairs. -/
theorem X1Split48A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A0X0Y0Certs
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
  · exact X1Split48A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0X0_pairs. -/
theorem X1Split48A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A0_pairs. -/
theorem X1Split48A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 5 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split48A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1X0Y0_check. -/
theorem X1Split48A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1X0Y0_pairs. -/
theorem X1Split48A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A1X0Y0Certs
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
  · exact X1Split48A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1X0_pairs. -/
theorem X1Split48A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A1_pairs. -/
theorem X1Split48A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 5 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split48A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2X0Y0_check. -/
theorem X1Split48A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2X0Y0_pairs. -/
theorem X1Split48A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A2X0Y0Certs
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
  · exact X1Split48A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2X0_pairs. -/
theorem X1Split48A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A2_pairs. -/
theorem X1Split48A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 5 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split48A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3X0Y0_check. -/
theorem X1Split48A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3X0Y0_pairs. -/
theorem X1Split48A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split48A3X0Y0Certs
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
  · exact X1Split48A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3X0_pairs. -/
theorem X1Split48A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split48A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split48A3_pairs. -/
theorem X1Split48A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 5 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split48A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0X0Y0_check. -/
theorem X1Split49A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0X0Y0_pairs. -/
theorem X1Split49A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A0X0Y0Certs
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
  · exact X1Split49A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0X0_pairs. -/
theorem X1Split49A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A0_pairs. -/
theorem X1Split49A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 6 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1X0Y0_check. -/
theorem X1Split49A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1X0Y0_pairs. -/
theorem X1Split49A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A1X0Y0Certs
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
  · exact X1Split49A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1X0_pairs. -/
theorem X1Split49A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A1_pairs. -/
theorem X1Split49A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 6 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2X0Y0_check. -/
theorem X1Split49A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2X0Y0_pairs. -/
theorem X1Split49A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A2X0Y0Certs
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
  · exact X1Split49A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2X0_pairs. -/
theorem X1Split49A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A2_pairs. -/
theorem X1Split49A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 6 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split49A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3X0Y0_check. -/
theorem X1Split49A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3X0Y0_pairs. -/
theorem X1Split49A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split49A3X0Y0Certs
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
  · exact X1Split49A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3X0_pairs. -/
theorem X1Split49A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split49A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split49A3_pairs. -/
theorem X1Split49A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 6 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split49A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split50A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0X0Y0_check. -/
theorem X1Split50A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split50A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0X0Y0_pairs. -/
theorem X1Split50A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 8 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split50A0X0Y0Certs
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
  · exact X1Split50A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0X0_pairs. -/
theorem X1Split50A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 8 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split50A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split50A0_pairs. -/
theorem X1Split50A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 8 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split50A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split51A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0X0Y0_check. -/
theorem X1Split51A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split51A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0X0Y0_pairs. -/
theorem X1Split51A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split51A0X0Y0Certs
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
  · exact X1Split51A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0X0_pairs. -/
theorem X1Split51A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split51A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split51A0_pairs. -/
theorem X1Split51A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split51A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split52A0X0Y0_check. -/
theorem X1Split52A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split52A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split52A0X0Y0_pairs. -/
theorem X1Split52A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split52A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M1Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split52A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split52A0X0_pairs. -/
theorem X1Split52A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split52A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
  (1918, 3507), (1924, 901), (1941, 3394)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0Y0_check. -/
theorem X1Split53A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split53A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0Y0_pairs. -/
theorem X1Split53A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split53A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M1Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split53A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split53A0X0Y1Certs : List (Nat × Nat) := [
  (11, 622), (186, 2539), (206, 3103), (211, 2957), (213, 2409),
  (220, 2907), (224, 2357), (301, 2245), (456, 2566), (463, 3014),
  (482, 2186), (508, 2408), (510, 2958), (607, 2150), (663, 2450),
  (805, 2304), (897, 1331), (898, 2533), (902, 948), (973, 2782),
  (1043, 3321), (1048, 2809), (1060, 3379), (1065, 2694), (1066, 3479),
  (1154, 2801), (1160, 2732), (1165, 3400), (1166, 1688), (1171, 3478),
  (1263, 1488), (1339, 3064), (1543, 2922), (1550, 1933), (1574, 3016),
  (1581, 1877), (1582, 1982), (1584, 1371), (1585, 2175), (1647, 1705),
  (1685, 3477), (1691, 3499), (1696, 2697), (1766, 3398), (1777, 2800),
  (1783, 3280), (1794, 2714), (1795, 3474), (1894, 3395), (1895, 1710),
  (1900, 3473), (1983, 3508), (1992, 1682), (1993, 3403), (1998, 2691),
  (1999, 2811), (2004, 3274)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0Y1_check. -/
theorem X1Split53A0X0Y1_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M1LeftColumns X1M1RightColumns) X1Split53A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0Y1_pairs. -/
theorem X1Split53A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M1LeftColumns X1M1RightColumns) X1Split53A0X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M1Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split53A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split53A0X0_pairs. -/
theorem X1Split53A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split53A0X0Y0_pairs x hx y hy hw
  · exact X1Split53A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y0Certs : List (Nat × Nat) := [
  (165, 227), (351, 329), (516, 381), (661, 405), (677, 410),
  (723, 436), (1676, 608)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y0_check. -/
theorem X1Split54A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y0_pairs. -/
theorem X1Split54A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk0_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · exact X1Split54A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y1Certs : List (Nat × Nat) := [
  (110, 670), (397, 708), (401, 710), (726, 777), (740, 780),
  (742, 781), (781, 788), (797, 792)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y1_check. -/
theorem X1Split54A0X0Y1_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y1_pairs. -/
theorem X1Split54A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk1_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk1
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk1_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · exact X1Split54A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y2Certs : List (Nat × Nat) := [
  (21, 863), (180, 878), (221, 890), (235, 892), (237, 893),
  (275, 898), (281, 900), (681, 930), (697, 935), (735, 941),
  (737, 942), (746, 947), (752, 949), (925, 1003)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y2_check. -/
theorem X1Split54A0X0Y2_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y2_pairs. -/
theorem X1Split54A0X0Y2_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y2Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk2_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk2
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk2_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · exact X1Split54A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y3Certs : List (Nat × Nat) := [
  (153, 1145), (318, 1160), (334, 1165)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y3_check. -/
theorem X1Split54A0X0Y3_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y3_pairs. -/
theorem X1Split54A0X0Y3_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y3Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk3_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk3
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk3_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · exact X1Split54A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y4Certs : List (Nat × Nat) := [
  (152, 1289), (1056, 1352), (1077, 1357)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y4_check. -/
theorem X1Split54A0X0Y4_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y4_pairs. -/
theorem X1Split54A0X0Y4_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y4Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk4_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk4
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk4_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · exact X1Split54A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y5Certs : List (Nat × Nat) := [
  (543, 1472), (1241, 1537), (1249, 1540)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y5_check. -/
theorem X1Split54A0X0Y5_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y5_pairs. -/
theorem X1Split54A0X0Y5_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk5,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y5Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk5_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk5
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk5_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · exact X1Split54A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y6Certs : List (Nat × Nat) := [
  (21, 1595), (166, 1621), (182, 1623), (235, 1634), (681, 1671),
  (695, 1673), (697, 1674), (735, 1679), (741, 1681), (748, 1686),
  (752, 1687), (757, 1689), (817, 1699), (833, 1704), (882, 1712),
  (888, 1713), (963, 1724)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y6_check. -/
theorem X1Split54A0X0Y6_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y6_pairs. -/
theorem X1Split54A0X0Y6_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk6,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y6Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk6_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk6
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk6_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · exact X1Split54A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y7Certs : List (Nat × Nat) := [
  (390, 1844), (542, 1860), (1075, 1915), (1339, 1947), (1352, 1948),
  (1551, 1978)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y7_check. -/
theorem X1Split54A0X0Y7_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y7_pairs. -/
theorem X1Split54A0X0Y7_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk7,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y7Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk7_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk7
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk7_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · exact X1Split54A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y8Certs : List (Nat × Nat) := [
  (661, 2113), (1069, 2134), (1096, 2139), (1361, 2173)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y8_check. -/
theorem X1Split54A0X0Y8_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y8_pairs. -/
theorem X1Split54A0X0Y8_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk8,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y8Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk8_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk8
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk8_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · exact X1Split54A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y9Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y9_check. -/
theorem X1Split54A0X0Y9_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y9_pairs. -/
theorem X1Split54A0X0Y9_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk9,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y9Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk9_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk9
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk9_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · exact X1Split54A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y10Certs : List (Nat × Nat) := [
  (129, 2309), (1000, 2405), (1517, 2447)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y10_check. -/
theorem X1Split54A0X0Y10_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y10_pairs. -/
theorem X1Split54A0X0Y10_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk10,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y10Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk10_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk10
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk10_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · exact X1Split54A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y11Certs : List (Nat × Nat) := [
  (482, 2556), (495, 2560), (515, 2563)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y11_check. -/
theorem X1Split54A0X0Y11_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y11Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y11_pairs. -/
theorem X1Split54A0X0Y11_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk11,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y11Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk11_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk11
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk11_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · exact X1Split54A0X0Y11_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y12Certs : List (Nat × Nat) := [
  (21, 2603), (235, 2639), (237, 2640), (697, 2686), (735, 2689),
  (737, 2690), (752, 2695), (817, 2704), (871, 2713), (882, 2716),
  (884, 2717), (893, 2720), (1788, 2775), (1832, 2781), (1839, 2783),
  (1843, 2784), (1848, 2787), (1907, 2792), (1909, 2793), (1918, 2797),
  (1919, 2799), (1930, 2807), (1936, 2810), (1941, 2813)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y12_check. -/
theorem X1Split54A0X0Y12_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y12Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y12_pairs. -/
theorem X1Split54A0X0Y12_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk12,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y12Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk12_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk12
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk12_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · exact X1Split54A0X0Y12_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y13Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y13_check. -/
theorem X1Split54A0X0Y13_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y13Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y13_pairs. -/
theorem X1Split54A0X0Y13_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk13,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y13Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk13_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk13
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk13_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · exact X1Split54A0X0Y13_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y14Certs : List (Nat × Nat) := [
  (386, 2933), (466, 2949), (1746, 3035)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y14_check. -/
theorem X1Split54A0X0Y14_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y14Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y14_pairs. -/
theorem X1Split54A0X0Y14_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk14,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y14Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk14_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk14
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk14_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · exact X1Split54A0X0Y14_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y15Certs : List (Nat × Nat) := [
  (205, 3065), (244, 3071), (512, 3099), (629, 3122), (672, 3128)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y15_check. -/
theorem X1Split54A0X0Y15_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y15Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y15_pairs. -/
theorem X1Split54A0X0Y15_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk15,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y15Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk15_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk15
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk15_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · exact X1Split54A0X0Y15_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y16Certs : List (Nat × Nat) := [
  (21, 3192), (166, 3214), (237, 3229), (275, 3232), (681, 3266),
  (737, 3273), (741, 3276), (757, 3279), (817, 3294), (831, 3299),
  (871, 3303), (873, 3304), (884, 3305), (888, 3307), (893, 3309),
  (952, 3316), (963, 3319), (1826, 3378), (1843, 3382), (1909, 3389),
  (1913, 3391), (1918, 3392), (1935, 3399), (1936, 3402)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y16_check. -/
theorem X1Split54A0X0Y16_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y16Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y16_pairs. -/
theorem X1Split54A0X0Y16_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk16,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y16Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk16_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk16
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk16_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · exact X1Split54A0X0Y16_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split54A0X0Y17Certs : List (Nat × Nat) := [
  (956, 3453), (958, 3454), (962, 3455), (967, 3460), (973, 3461),
  (978, 3462), (1048, 3470), (1049, 3472), (1054, 3475), (1060, 3476),
  (1066, 3481), (1071, 3484), (1154, 3493), (1156, 3494), (1160, 3496),
  (1165, 3498), (1171, 3504), (1172, 3506)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y17_check. -/
theorem X1Split54A0X0Y17_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y17Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0Y17_pairs. -/
theorem X1Split54A0X0Y17_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk17,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      X1M0LeftColumns X1M0RightColumns) X1Split54A0X0Y17Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk17_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks4S2048Chunk17
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk17_bound
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
      exact X1M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · exact X1Split54A0X0Y17_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split54A0X0_pairs. -/
theorem X1Split54A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X1Split54A0X0Y0_pairs x hx y hy hw
  · exact X1Split54A0X0Y1_pairs x hx y hy hw
  · exact X1Split54A0X0Y2_pairs x hx y hy hw
  · exact X1Split54A0X0Y3_pairs x hx y hy hw
  · exact X1Split54A0X0Y4_pairs x hx y hy hw
  · exact X1Split54A0X0Y5_pairs x hx y hy hw
  · exact X1Split54A0X0Y6_pairs x hx y hy hw
  · exact X1Split54A0X0Y7_pairs x hx y hy hw
  · exact X1Split54A0X0Y8_pairs x hx y hy hw
  · exact X1Split54A0X0Y9_pairs x hx y hy hw
  · exact X1Split54A0X0Y10_pairs x hx y hy hw
  · exact X1Split54A0X0Y11_pairs x hx y hy hw
  · exact X1Split54A0X0Y12_pairs x hx y hy hw
  · exact X1Split54A0X0Y13_pairs x hx y hy hw
  · exact X1Split54A0X0Y14_pairs x hx y hy hw
  · exact X1Split54A0X0Y15_pairs x hx y hy hw
  · exact X1Split54A0X0Y16_pairs x hx y hy hw
  · exact X1Split54A0X0Y17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split55A0X0Y0Certs : List (Nat × Nat) := [
  (21, 118), (180, 326), (221, 370), (235, 379), (237, 380),
  (275, 402), (281, 409), (695, 756), (748, 787), (757, 799),
  (817, 851), (831, 861), (833, 862), (873, 875), (882, 887),
  (884, 889), (888, 891), (954, 929), (964, 946), (1786, 1594),
  (1826, 1618), (1828, 1620), (1832, 1622), (1839, 1630), (1918, 1678),
  (1924, 1696), (1930, 1703), (1941, 1722)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0Y0_check. -/
theorem X1Split55A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split55A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0Y0_pairs. -/
theorem X1Split55A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split55A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split55A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split55A0X0Y1Certs : List (Nat × Nat) := [
  (902, 2590), (956, 2625), (967, 2635), (969, 2638), (978, 2646),
  (1039, 2681), (1043, 2684), (1048, 2688), (1049, 2692), (1060, 2708),
  (1065, 2712), (1154, 2770), (1165, 2778), (1171, 2791), (1647, 3191),
  (1691, 3216), (1696, 3224), (1766, 3264), (1768, 3265), (1777, 3272),
  (1785, 3293), (1789, 3298), (1800, 3315), (1889, 3372), (1894, 3377),
  (1895, 3380), (1900, 3388), (1901, 3396), (1983, 3446), (1992, 3452),
  (1998, 3466), (2004, 3492)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0Y1_check. -/
theorem X1Split55A0X0Y1_check : checkGrid m4TX1 censusX1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split55A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0Y1_pairs. -/
theorem X1Split55A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split55A0X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split55A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split55A0X0_pairs. -/
theorem X1Split55A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split55A0X0Y0_pairs x hx y hy hw
  · exact X1Split55A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split56A0X0Y0Certs : List (Nat × Nat) := [
  (4, 51), (25, 152), (33, 184), (55, 307), (61, 325),
  (77, 401), (87, 452), (101, 530), (138, 743), (148, 785),
  (170, 927), (186, 1046), (206, 1196), (253, 1574), (259, 1590),
  (271, 1695), (297, 1943), (322, 2191), (351, 2583), (353, 2586),
  (363, 2631), (404, 3109), (408, 3177), (412, 3187), (424, 3290)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split56A0X0Y0_check. -/
theorem X1Split56A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split56A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split56A0X0Y0_pairs. -/
theorem X1Split56A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split56A0X0Y0Certs
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
  · exact X1Split56A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split56A0X0_pairs. -/
theorem X1Split56A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split56A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split57A0X0Y0Certs : List (Nat × Nat) := [
  (1, 19), (3, 42), (4, 65), (5, 87), (7, 138),
  (8, 166), (9, 207), (10, 249), (13, 425), (14, 489),
  (15, 558), (16, 638), (19, 957), (20, 1102), (21, 1244),
  (22, 1392), (24, 1769), (25, 2029), (26, 2261), (28, 2859)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0X0Y0_check. -/
theorem X1Split57A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split57A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0X0Y0_pairs. -/
theorem X1Split57A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split57A0X0Y0Certs
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
  · exact X1Split57A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0X0_pairs. -/
theorem X1Split57A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split57A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split57A0_pairs. -/
theorem X1Split57A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split57A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split58A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0X0Y0_check. -/
theorem X1Split58A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split58A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0X0Y0_pairs. -/
theorem X1Split58A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 8 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split58A0X0Y0Certs
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
  · exact X1Split58A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0X0_pairs. -/
theorem X1Split58A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 8 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split58A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split58A0_pairs. -/
theorem X1Split58A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 8 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split58A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split59A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0X0Y0_check. -/
theorem X1Split59A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split59A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0X0Y0_pairs. -/
theorem X1Split59A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split59A0X0Y0Certs
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
  · exact X1Split59A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0X0_pairs. -/
theorem X1Split59A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split59A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split59A0_pairs. -/
theorem X1Split59A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 7 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split59A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split60A0X0Y0Certs : List (Nat × Nat) := [
  (44, 1884), (56, 3132), (125, 1384), (140, 1543), (244, 2341),
  (264, 2251), (280, 2246), (295, 2564), (423, 3023), (429, 1078),
  (466, 3092), (478, 3142), (607, 2364), (615, 2008), (638, 2410),
  (652, 3100), (763, 1323), (771, 2536), (841, 1983), (859, 1386)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0X0Y0_check. -/
theorem X1Split60A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split60A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0X0Y0_pairs. -/
theorem X1Split60A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split60A0X0Y0Certs
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
  · exact X1Split60A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0X0_pairs. -/
theorem X1Split60A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split60A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split60A0_pairs. -/
theorem X1Split60A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split60A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split61A0X0Y0_check. -/
theorem X1Split61A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split61A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split61A0X0Y0_pairs. -/
theorem X1Split61A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split61A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact X1M1Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split61A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split61A0X0_pairs. -/
theorem X1Split61A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split61A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split62A0X0Y0Certs : List (Nat × Nat) := [
  (2141, 3095), (2321, 1013), (2413, 1367), (3126, 1848), (3540, 1485),
  (6836, 2295), (8652, 2935), (9114, 1882), (9250, 1158), (9323, 2096),
  (12013, 2021), (16122, 478), (16605, 2938), (16746, 2366), (16783, 1461),
  (16862, 1081), (17276, 1880), (17336, 3012), (17865, 2427), (17962, 1846),
  (18224, 2465), (18324, 1966), (18371, 1823), (18715, 1072), (18805, 535),
  (18829, 595), (19218, 1909), (19640, 719), (19752, 1175), (19780, 2253),
  (28739, 712), (29605, 1191), (29679, 1424), (29690, 1965), (29870, 1328),
  (29974, 2431), (30096, 2013), (30408, 3123), (30469, 2407), (30900, 2165),
  (31024, 698), (31423, 1042), (31522, 1557), (31809, 1998), (31995, 1207),
  (32008, 2495), (32034, 1322), (40622, 2354), (40788, 2143), (40795, 510),
  (40877, 1921), (41499, 2414), (41670, 3145), (41732, 1544), (42024, 2491),
  (42564, 2956), (42842, 993), (43046, 1874), (43556, 238), (43767, 1552),
  (44018, 2889), (44025, 2436), (44253, 1523), (44262, 1949), (45404, 2469),
  (48764, 1975), (50733, 1958), (50764, 3084), (51242, 1208), (51651, 3075),
  (51664, 1162), (51682, 1193), (51841, 1981), (52154, 1422), (53349, 2421),
  (56739, 2174), (56999, 2989), (57284, 1459), (57351, 3059), (58335, 1141),
  (58392, 2210)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0Y0_check. -/
theorem X1Split62A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split62A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0Y0_pairs. -/
theorem X1Split62A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split62A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S256Chunk0 masks3S2048Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M1Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split62A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split62A0X0Y1Certs : List (Nat × Nat) := [
  (2208, 461), (2217, 630), (2319, 2236), (2393, 2205), (2422, 3139),
  (2550, 2331), (2704, 508), (2917, 2198), (2936, 2534), (3468, 2285),
  (8153, 1059), (8257, 288), (8267, 1388), (8355, 2473), (8394, 1212),
  (9409, 981), (9436, 2926), (9446, 3120), (9574, 3134), (9616, 2299),
  (9734, 1029), (16320, 284), (16396, 1058), (16672, 3068), (17102, 2107),
  (17103, 1210), (17155, 3140), (17862, 1031), (18410, 1837), (18453, 1500),
  (18654, 2132), (18786, 3004), (19179, 2216), (21498, 2673), (27663, 1096),
  (28730, 1497), (28805, 1279), (29163, 3026), (29176, 2213), (29330, 2090),
  (29381, 1172), (29973, 1807), (30089, 1911), (30641, 1886), (31048, 2152),
  (31201, 3111), (31927, 3062), (32089, 2178), (34543, 3361), (40317, 1918),
  (41187, 1452), (41242, 2182), (41417, 2374), (41499, 2130), (41577, 2994),
  (41986, 2147), (42059, 527), (42953, 1935), (43114, 2494), (43531, 2209),
  (43549, 2329), (43583, 1378), (44337, 3090), (51030, 1952), (51306, 2952),
  (51352, 3060), (51399, 2565), (51501, 2550), (52456, 2418), (52498, 3003),
  (57188, 2925), (57207, 2136), (57232, 2185), (57490, 2332), (57638, 2342),
  (58304, 1989), (58432, 3113), (58507, 1314), (58546, 1870)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0Y1_check. -/
theorem X1Split62A0X0Y1_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      X1M1LeftColumns X1M1RightColumns) X1Split62A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0Y1_pairs. -/
theorem X1Split62A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      X1M1LeftColumns X1M1RightColumns) X1Split62A0X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks1S256Chunk0 masks3S2048Chunk1
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M1Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split62A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split62A0X0_pairs. -/
theorem X1Split62A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split62A0X0Y0_pairs x hx y hy hw
  · exact X1Split62A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split63A0X0Y0Certs : List (Nat × Nat) := [
  (1924, 1697), (2141, 234), (2413, 509), (2583, 627), (2702, 720),
  (3025, 992), (3201, 1134), (3298, 1209), (3468, 1321), (3694, 1484),
  (3764, 1533), (3779, 1550), (3782, 1554), (4230, 328), (8194, 221),
  (8212, 232), (8242, 276), (8430, 469), (8652, 623), (9079, 982),
  (9091, 987), (9100, 994), (9323, 1161), (9532, 1320), (9635, 1383),
  (9744, 1467), (9865, 1559), (12896, 791), (14480, 449), (16518, 457),
  (16605, 534), (16732, 607), (17204, 1002), (17246, 1030), (17336, 1116),
  (17376, 1137), (17621, 1311), (17647, 1327), (17824, 1457), (18368, 282),
  (18725, 598), (18771, 620), (18790, 654), (18864, 699), (19312, 1071),
  (19370, 1121), (19464, 1185), (19553, 1262), (19752, 1377), (20848, 676),
  (23227, 940), (24103, 1629), (24569, 408), (26224, 1711), (27369, 1035),
  (28480, 275), (28922, 660), (29419, 1052), (29568, 1169), (29570, 1170),
  (29605, 1206), (29697, 1276), (29705, 1284), (29850, 1350), (29922, 1433),
  (29924, 1434), (29970, 1458), (30379, 97), (30451, 218), (30657, 440),
  (30844, 587), (31020, 709), (31028, 716), (31452, 1066), (31674, 1227),
  (31825, 1334), (31895, 1373), (31954, 1437), (32087, 1524), (34051, 1481),
  (35165, 798), (36315, 1669), (37396, 945), (38260, 1619), (40866, 506),
  (40883, 525), (40925, 551), (40957, 581), (41125, 697), (41984, 1348),
  (42108, 1451), (42564, 176), (42623, 236), (42667, 289), (42921, 536),
  (42999, 594), (43114, 679), (43160, 706), (43522, 1010), (43694, 1142),
  (43929, 1308), (44242, 1532), (44249, 1539), (44255, 1547), (44261, 1551),
  (48493, 1721), (50977, 503), (51191, 663), (51682, 1050), (51822, 1155),
  (51839, 1173), (51852, 1188), (51918, 1231), (51934, 1260), (52012, 1301),
  (52026, 1309), (52181, 1430), (52223, 1450), (52324, 1522), (55521, 874),
  (56714, 153), (56739, 185), (56780, 226), (56967, 435), (56982, 447),
  (57678, 1000), (57858, 1140), (57864, 1143), (58130, 1329), (58310, 1460),
  (59391, 755)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0Y0_check. -/
theorem X1Split63A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split63A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0Y0_pairs. -/
theorem X1Split63A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split63A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact X1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact X1Split63A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split63A0X0Y1Certs : List (Nat × Nat) := [
  (1043, 2685), (1631, 3178), (2062, 1802), (2165, 1871), (2442, 2109),
  (2619, 2278), (2625, 2284), (2691, 2326), (2693, 2327), (2926, 2551),
  (2933, 2558), (3295, 2876), (3369, 2920), (4974, 2589), (5967, 3381),
  (6708, 2294), (8244, 1847), (8529, 2098), (8671, 2211), (8766, 2306),
  (8812, 2348), (8967, 2472), (9036, 2552), (9407, 2883), (9591, 2999),
  (9643, 3028), (10230, 1818), (13281, 2711), (13863, 3190), (16301, 1796),
  (16387, 1845), (16397, 1855), (16413, 1866), (16416, 1869), (16688, 2105),
  (16697, 2111), (16912, 2307), (17067, 2430), (17712, 2983), (17714, 2984),
  (17831, 3055), (17860, 3086), (18378, 1825), (18412, 1838), (18428, 1849),
  (18653, 2073), (18786, 2135), (18877, 2233), (19117, 2440), (19136, 2457),
  (19139, 2461), (19177, 2513), (19795, 3009), (19812, 3020), (19926, 3143),
  (24087, 3217), (26198, 3263), (28536, 1808), (28539, 1809), (28622, 1859),
  (28688, 1910), (28805, 2058), (28899, 2101), (28956, 2126), (29274, 2425),
  (29996, 3022), (30006, 3033), (30064, 3076), (30784, 1994), (30870, 2074),
  (31033, 2169), (31048, 2194), (31166, 2310), (31169, 2314), (31212, 2350),
  (31801, 2878), (31825, 2895), (31926, 2962), (32089, 3066), (35672, 2707),
  (37702, 2702), (38871, 1917), (40892, 1905), (40894, 1906), (40945, 1956),
  (41037, 2069), (41190, 2144), (41193, 2145), (41242, 2208), (41409, 2363),
  (41420, 2375), (41423, 2376), (41493, 2426), (41580, 2516), (42059, 2924),
  (42071, 2934), (42202, 3015), (42258, 3053), (42994, 1980), (43243, 2164),
  (43315, 2235), (43467, 2380), (43506, 2399), (43630, 2537), (44087, 2919),
  (44143, 2963), (44337, 3110), (45612, 2464), (47984, 2771), (48524, 3223),
  (49098, 1974), (50909, 1790), (50922, 1800), (50924, 1801), (51205, 2060),
  (51259, 2087), (51663, 2416), (52267, 2953), (52461, 3077), (52465, 3080),
  (52498, 3137), (53688, 2401), (56126, 2769), (56959, 3449), (57232, 1951),
  (57244, 1977), (57464, 2128), (57488, 2148), (57507, 2179), (57573, 2240),
  (57699, 2365), (57765, 2406), (57879, 2529), (58355, 2932), (58373, 2950),
  (58439, 2986), (58441, 2988), (60751, 3231), (61027, 3445)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0Y1_check. -/
theorem X1Split63A0X0Y1_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split63A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0Y1_pairs. -/
theorem X1Split63A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split63A0X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact X1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact X1Split63A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split63A0X0_pairs. -/
theorem X1Split63A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split63A0X0Y0_pairs x hx y hy hw
  · exact X1Split63A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

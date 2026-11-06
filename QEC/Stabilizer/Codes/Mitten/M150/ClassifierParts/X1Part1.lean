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
def X1Split16A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0X0Y0_check. -/
theorem X1Split16A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split16A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0X0Y0_pairs. -/
theorem X1Split16A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split16A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split16A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0X0_pairs. -/
theorem X1Split16A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split16A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split16A0_pairs. -/
theorem X1Split16A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 2 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split16A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0X0Y0_check. -/
theorem X1Split17A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0X0Y0_pairs. -/
theorem X1Split17A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A0X0Y0Certs
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
  · exact X1Split17A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0X0_pairs. -/
theorem X1Split17A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A0_pairs. -/
theorem X1Split17A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 2 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1X0Y0_check. -/
theorem X1Split17A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1X0Y0_pairs. -/
theorem X1Split17A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A1X0Y0Certs
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
  · exact X1Split17A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1X0_pairs. -/
theorem X1Split17A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A1_pairs. -/
theorem X1Split17A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 2 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2X0Y0_check. -/
theorem X1Split17A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2X0Y0_pairs. -/
theorem X1Split17A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A2X0Y0Certs
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
  · exact X1Split17A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2X0_pairs. -/
theorem X1Split17A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A2_pairs. -/
theorem X1Split17A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 2 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split17A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3X0Y0_check. -/
theorem X1Split17A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3X0Y0_pairs. -/
theorem X1Split17A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split17A3X0Y0Certs
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
  · exact X1Split17A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3X0_pairs. -/
theorem X1Split17A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split17A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split17A3_pairs. -/
theorem X1Split17A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 2 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split17A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split18A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0X0Y0_check. -/
theorem X1Split18A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split18A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0X0Y0_pairs. -/
theorem X1Split18A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split18A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact X1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split18A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0X0_pairs. -/
theorem X1Split18A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split18A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split18A0_pairs. -/
theorem X1Split18A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 2 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split18A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0X0Y0_check. -/
theorem X1Split19A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0X0Y0_pairs. -/
theorem X1Split19A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A0X0Y0Certs
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
  · exact X1Split19A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0X0_pairs. -/
theorem X1Split19A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A0_pairs. -/
theorem X1Split19A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1X0Y0_check. -/
theorem X1Split19A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1X0Y0_pairs. -/
theorem X1Split19A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A1X0Y0Certs
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
  · exact X1Split19A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1X0_pairs. -/
theorem X1Split19A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A1_pairs. -/
theorem X1Split19A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2X0Y0_check. -/
theorem X1Split19A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2X0Y0_pairs. -/
theorem X1Split19A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A2X0Y0Certs
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
  · exact X1Split19A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2X0_pairs. -/
theorem X1Split19A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A2_pairs. -/
theorem X1Split19A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split19A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3X0Y0_check. -/
theorem X1Split19A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3X0Y0_pairs. -/
theorem X1Split19A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split19A3X0Y0Certs
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
  · exact X1Split19A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3X0_pairs. -/
theorem X1Split19A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split19A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split19A3_pairs. -/
theorem X1Split19A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split19A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0X0Y0_check. -/
theorem X1Split20A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0X0Y0_pairs. -/
theorem X1Split20A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A0X0Y0Certs
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
  · exact X1Split20A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0X0_pairs. -/
theorem X1Split20A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A0_pairs. -/
theorem X1Split20A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 3 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1X0Y0_check. -/
theorem X1Split20A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1X0Y0_pairs. -/
theorem X1Split20A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A1X0Y0Certs
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
  · exact X1Split20A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1X0_pairs. -/
theorem X1Split20A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A1_pairs. -/
theorem X1Split20A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 3 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2X0Y0_check. -/
theorem X1Split20A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2X0Y0_pairs. -/
theorem X1Split20A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A2X0Y0Certs
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
  · exact X1Split20A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2X0_pairs. -/
theorem X1Split20A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A2_pairs. -/
theorem X1Split20A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 3 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split20A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3X0Y0_check. -/
theorem X1Split20A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3X0Y0_pairs. -/
theorem X1Split20A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split20A3X0Y0Certs
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
  · exact X1Split20A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3X0_pairs. -/
theorem X1Split20A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split20A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split20A3_pairs. -/
theorem X1Split20A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 3 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split20A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0X0Y0_check. -/
theorem X1Split21A0X0Y0_check : checkGrid m4TX1 censusX1 2 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0X0Y0_pairs. -/
theorem X1Split21A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A0X0Y0Certs
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
  · exact X1Split21A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0X0_pairs. -/
theorem X1Split21A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A0_pairs. -/
theorem X1Split21A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 0) = 4 →
      sweepAccept m4TX1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1X0Y0_check. -/
theorem X1Split21A1X0Y0_check : checkGrid m4TX1 censusX1 2 91076351 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1X0Y0_pairs. -/
theorem X1Split21A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 91076351 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A1X0Y0Certs
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
  · exact X1Split21A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1X0_pairs. -/
theorem X1Split21A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A1_pairs. -/
theorem X1Split21A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 91076351) = 4 →
      sweepAccept m4TX1 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2X0Y0_check. -/
theorem X1Split21A2X0Y0_check : checkGrid m4TX1 censusX1 2 985062231 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2X0Y0_pairs. -/
theorem X1Split21A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 985062231 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A2X0Y0Certs
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
  · exact X1Split21A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2X0_pairs. -/
theorem X1Split21A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A2_pairs. -/
theorem X1Split21A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 985062231) = 4 →
      sweepAccept m4TX1 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split21A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3X0Y0_check. -/
theorem X1Split21A3X0Y0_check : checkGrid m4TX1 censusX1 2 1071345064 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3X0Y0_pairs. -/
theorem X1Split21A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX1 censusX1 2 1071345064 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M2LeftColumns X1M2RightColumns) X1Split21A3X0Y0Certs
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
  · exact X1Split21A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3X0_pairs. -/
theorem X1Split21A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split21A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split21A3_pairs. -/
theorem X1Split21A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 2 x y 1071345064) = 4 →
      sweepAccept m4TX1 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split21A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split22A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0X0Y0_check. -/
theorem X1Split22A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split22A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0X0Y0_pairs. -/
theorem X1Split22A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split22A0X0Y0Certs
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
  · exact X1Split22A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0X0_pairs. -/
theorem X1Split22A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split22A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split22A0_pairs. -/
theorem X1Split22A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split22A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split23A0X0Y0Certs : List (Nat × Nat) := [
  (0, 3505), (2, 3502), (6, 3486), (11, 1714), (12, 3393),
  (17, 2719), (18, 2798), (23, 3306), (27, 879), (29, 793)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0X0Y0_check. -/
theorem X1Split23A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split23A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0X0Y0_pairs. -/
theorem X1Split23A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split23A0X0Y0Certs
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
  · exact X1Split23A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0X0_pairs. -/
theorem X1Split23A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split23A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split23A0_pairs. -/
theorem X1Split23A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split23A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split24A0X0Y0Certs : List (Nat × Nat) := [
  (1, 800), (15, 1709), (17, 1728), (66, 2628), (68, 2693),
  (72, 2806), (147, 2772), (153, 3218), (155, 3278), (159, 3397),
  (165, 3447), (264, 3373), (270, 3450), (362, 1639), (368, 2647),
  (374, 3234), (417, 1723), (423, 2729), (429, 3317), (433, 951)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split24A0X0Y0_check. -/
theorem X1Split24A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split24A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split24A0X0Y0_pairs. -/
theorem X1Split24A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split24A0X0Y0Certs
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
  · exact X1Split24A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split24A0X0_pairs. -/
theorem X1Split24A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split24A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split25A0X0Y0Certs : List (Nat × Nat) := [
  (8, 77), (39, 148), (109, 228), (153, 283), (166, 314),
  (277, 404), (311, 448), (397, 518), (542, 611), (661, 711),
  (697, 757), (735, 776), (741, 779), (893, 897), (952, 928),
  (958, 933), (1056, 1033), (1241, 1177), (1516, 1356), (1746, 1541),
  (1772, 1580), (1837, 1628), (1843, 1633), (1909, 1670), (1919, 1685),
  (1935, 1708)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0Y0_check. -/
theorem X1Split25A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split25A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0Y0_pairs. -/
theorem X1Split25A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split25A0X0Y0Certs
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
  · exact X1Split25A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split25A0X0Y1Certs : List (Nat × Nat) := [
  (186, 1914), (211, 1945), (213, 1946), (482, 2156), (898, 2561),
  (918, 2602), (962, 2627), (1037, 2680), (1056, 2703), (1066, 2715),
  (1160, 2774), (1172, 2805), (1574, 3097), (1582, 3112), (1585, 3118),
  (1645, 3189), (1687, 3213), (1702, 3228), (1778, 3277), (1783, 3291),
  (1794, 3302), (1885, 3370), (1981, 3444), (1993, 3459)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0Y1_check. -/
theorem X1Split25A0X0Y1_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split25A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0Y1_pairs. -/
theorem X1Split25A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split25A0X0Y1Certs
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
  · exact X1Split25A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split25A0X0_pairs. -/
theorem X1Split25A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact X1Split25A0X0Y0_pairs x hx y hy hw
  · exact X1Split25A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split26A0X0Y0Certs : List (Nat × Nat) := [
  (15, 112), (57, 312), (66, 365), (68, 368), (136, 735),
  (142, 754), (155, 847), (159, 860), (164, 872), (255, 1579),
  (264, 1617), (265, 1627), (357, 2600), (362, 2622), (368, 2679),
  (369, 2700), (406, 3171), (418, 3222), (423, 3261), (429, 3366)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split26A0X0Y0_check. -/
theorem X1Split26A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split26A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split26A0X0Y0_pairs. -/
theorem X1Split26A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split26A0X0Y0Certs
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
  · exact X1Split26A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split26A0X0_pairs. -/
theorem X1Split26A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split26A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split27A0X0Y0Certs : List (Nat × Nat) := [
  (0, 11), (2, 31), (6, 109), (11, 299), (12, 355),
  (17, 733), (18, 835), (23, 1573), (27, 2575), (29, 3168)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0X0Y0_check. -/
theorem X1Split27A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split27A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0X0Y0_pairs. -/
theorem X1Split27A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split27A0X0Y0Certs
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
  · exact X1Split27A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0X0_pairs. -/
theorem X1Split27A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split27A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split27A0_pairs. -/
theorem X1Split27A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split27A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split28A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0X0Y0_check. -/
theorem X1Split28A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split28A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0X0Y0_pairs. -/
theorem X1Split28A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split28A0X0Y0Certs
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
  · exact X1Split28A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0X0_pairs. -/
theorem X1Split28A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split28A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split28A0_pairs. -/
theorem X1Split28A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split28A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split29A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0X0Y0_check. -/
theorem X1Split29A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split29A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0X0Y0_pairs. -/
theorem X1Split29A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split29A0X0Y0Certs
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
  · exact X1Split29A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0X0_pairs. -/
theorem X1Split29A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split29A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split29A0_pairs. -/
theorem X1Split29A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split29A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split30A0X0Y0Certs : List (Nat × Nat) := [
  (33, 1924), (127, 2003), (245, 2475), (283, 2515), (430, 2483),
  (469, 450), (616, 2517), (654, 1037), (772, 680), (866, 1487)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0X0Y0_check. -/
theorem X1Split30A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split30A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0X0Y0_pairs. -/
theorem X1Split30A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split30A0X0Y0Certs
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
  · exact X1Split30A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0X0_pairs. -/
theorem X1Split30A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split30A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split30A0_pairs. -/
theorem X1Split30A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split30A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split31A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split31A0X0Y0_check. -/
theorem X1Split31A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split31A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split31A0X0Y0_pairs. -/
theorem X1Split31A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split31A0X0Y0Certs
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
  · exact X1Split31A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split31A0X0_pairs. -/
theorem X1Split31A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split31A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

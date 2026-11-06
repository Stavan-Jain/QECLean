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
def Z0Split48A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0X0Y0_check. -/
theorem Z0Split48A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split48A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0X0Y0_pairs. -/
theorem Z0Split48A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split48A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split48A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0X0_pairs. -/
theorem Z0Split48A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split48A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split48A0_pairs. -/
theorem Z0Split48A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split48A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split49A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0X0Y0_check. -/
theorem Z0Split49A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split49A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0X0Y0_pairs. -/
theorem Z0Split49A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split49A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split49A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0X0_pairs. -/
theorem Z0Split49A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split49A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split49A0_pairs. -/
theorem Z0Split49A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 6 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split49A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0X0Y0_check. -/
theorem Z0Split50A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0X0Y0_pairs. -/
theorem Z0Split50A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 8 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split50A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0X0_pairs. -/
theorem Z0Split50A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 8 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A0_pairs. -/
theorem Z0Split50A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 8 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1X0Y0_check. -/
theorem Z0Split50A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1X0Y0_pairs. -/
theorem Z0Split50A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 8 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split50A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1X0_pairs. -/
theorem Z0Split50A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 8 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A1_pairs. -/
theorem Z0Split50A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 8 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2X0Y0_check. -/
theorem Z0Split50A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2X0Y0_pairs. -/
theorem Z0Split50A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 8 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split50A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2X0_pairs. -/
theorem Z0Split50A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 8 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A2_pairs. -/
theorem Z0Split50A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 8 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split50A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3X0Y0_check. -/
theorem Z0Split50A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3X0Y0_pairs. -/
theorem Z0Split50A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 8 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split50A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split50A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3X0_pairs. -/
theorem Z0Split50A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 8 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split50A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split50A3_pairs. -/
theorem Z0Split50A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 8 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split50A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0X0Y0_check. -/
theorem Z0Split51A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0X0Y0_pairs. -/
theorem Z0Split51A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split51A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0X0_pairs. -/
theorem Z0Split51A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A0_pairs. -/
theorem Z0Split51A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1X0Y0_check. -/
theorem Z0Split51A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1X0Y0_pairs. -/
theorem Z0Split51A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split51A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1X0_pairs. -/
theorem Z0Split51A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A1_pairs. -/
theorem Z0Split51A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2X0Y0_check. -/
theorem Z0Split51A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2X0Y0_pairs. -/
theorem Z0Split51A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split51A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2X0_pairs. -/
theorem Z0Split51A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A2_pairs. -/
theorem Z0Split51A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split51A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3X0Y0_check. -/
theorem Z0Split51A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3X0Y0_pairs. -/
theorem Z0Split51A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split51A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split51A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3X0_pairs. -/
theorem Z0Split51A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split51A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split51A3_pairs. -/
theorem Z0Split51A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split51A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A0X0Y0Certs : List (Nat × Nat) := [
  (39, 0), (83, 1435), (176, 1868), (181, 1669), (238, 1383),
  (246, 0), (292, 1496), (332, 1665), (338, 1206)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A0X0Y0_check. -/
theorem Z0Split52A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A0X0Y0_pairs. -/
theorem Z0Split52A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split52A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A0X0_pairs. -/
theorem Z0Split52A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A1X0Y0Certs : List (Nat × Nat) := [
  (123, 2066), (129, 0), (234, 2028)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A1X0Y0_check. -/
theorem Z0Split52A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A1X0Y0_pairs. -/
theorem Z0Split52A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split52A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A1X0_pairs. -/
theorem Z0Split52A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A2X0Y0Certs : List (Nat × Nat) := [
  (118, 0), (286, 2282)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A2X0Y0_check. -/
theorem Z0Split52A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A2X0Y0_pairs. -/
theorem Z0Split52A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split52A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A2X0_pairs. -/
theorem Z0Split52A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split52A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A3X0Y0_check. -/
theorem Z0Split52A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A3X0Y0_pairs. -/
theorem Z0Split52A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split52A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split52A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split52A3X0_pairs. -/
theorem Z0Split52A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split52A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A0X0Y0Certs : List (Nat × Nat) := [
  (911, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0Y0_check. -/
theorem Z0Split53A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0Y0_pairs. -/
theorem Z0Split53A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split53A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A0X0Y1Certs : List (Nat × Nat) := [
  (555, 0), (827, 0), (1327, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0Y1_check. -/
theorem Z0Split53A0X0Y1_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0Y1_pairs. -/
theorem Z0Split53A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split53A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A0X0_pairs. -/
theorem Z0Split53A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split53A0X0Y0_pairs x hx y hy hw
  · exact Z0Split53A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A1X0Y0Certs : List (Nat × Nat) := [
  (191, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0Y0_check. -/
theorem Z0Split53A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0Y0_pairs. -/
theorem Z0Split53A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split53A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A1X0Y1Certs : List (Nat × Nat) := [
  (339, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0Y1_check. -/
theorem Z0Split53A1X0Y1_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A1X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0Y1_pairs. -/
theorem Z0Split53A1X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A1X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split53A1X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A1X0_pairs. -/
theorem Z0Split53A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split53A1X0Y0_pairs x hx y hy hw
  · exact Z0Split53A1X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A2X0Y0Certs : List (Nat × Nat) := [
  (1287, 0), (1839, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0Y0_check. -/
theorem Z0Split53A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0Y0_pairs. -/
theorem Z0Split53A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split53A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A2X0Y1Certs : List (Nat × Nat) := [
  (382, 0), (1741, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0Y1_check. -/
theorem Z0Split53A2X0Y1_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A2X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0Y1_pairs. -/
theorem Z0Split53A2X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A2X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split53A2X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A2X0_pairs. -/
theorem Z0Split53A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split53A2X0Y0_pairs x hx y hy hw
  · exact Z0Split53A2X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0Y0_check. -/
theorem Z0Split53A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0Y0_pairs. -/
theorem Z0Split53A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split53A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split53A3X0Y1Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0Y1_check. -/
theorem Z0Split53A3X0Y1_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A3X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0Y1_pairs. -/
theorem Z0Split53A3X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns) Z0Split53A3X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z0M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split53A3X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split53A3X0_pairs. -/
theorem Z0Split53A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split53A3X0Y0_pairs x hx y hy hw
  · exact Z0Split53A3X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y0Certs : List (Nat × Nat) := [
  (677, 307)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y0_check. -/
theorem Z0Split54A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y0_pairs. -/
theorem Z0Split54A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk0_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · exact Z0Split54A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y1Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y1_check. -/
theorem Z0Split54A0X0Y1_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y1_pairs. -/
theorem Z0Split54A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk1_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk1_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · exact Z0Split54A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y2Certs : List (Nat × Nat) := [
  (752, 719), (960, 775)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y2_check. -/
theorem Z0Split54A0X0Y2_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y2_pairs. -/
theorem Z0Split54A0X0Y2_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y2Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk2_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk2
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk2_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · exact Z0Split54A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y3Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y3_check. -/
theorem Z0Split54A0X0Y3_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y3_pairs. -/
theorem Z0Split54A0X0Y3_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y3Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk3_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk3
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk3_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · exact Z0Split54A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y4Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y4_check. -/
theorem Z0Split54A0X0Y4_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y4_pairs. -/
theorem Z0Split54A0X0Y4_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y4Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk4_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk4
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk4_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · exact Z0Split54A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y5Certs : List (Nat × Nat) := [
  (146, 1058), (1050, 1108), (1094, 1111)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y5_check. -/
theorem Z0Split54A0X0Y5_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y5_pairs. -/
theorem Z0Split54A0X0Y5_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y5Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk5_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk5
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk5_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · exact Z0Split54A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y6Certs : List (Nat × Nat) := [
  (882, 1240), (963, 1246)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y6_check. -/
theorem Z0Split54A0X0Y6_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y6_pairs. -/
theorem Z0Split54A0X0Y6_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y6Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk6_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk6
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk6_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · exact Z0Split54A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y7Certs : List (Nat × Nat) := [
  (299, 1354), (645, 1374)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y7_check. -/
theorem Z0Split54A0X0Y7_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y7_pairs. -/
theorem Z0Split54A0X0Y7_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y7Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk7_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk7
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk7_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · exact Z0Split54A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y8Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y8_check. -/
theorem Z0Split54A0X0Y8_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y8_pairs. -/
theorem Z0Split54A0X0Y8_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk8,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y8Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk8_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk8
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk8_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · exact Z0Split54A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y9Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y9_check. -/
theorem Z0Split54A0X0Y9_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y9_pairs. -/
theorem Z0Split54A0X0Y9_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk9,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y9Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk9_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk9
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk9_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · exact Z0Split54A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y10Certs : List (Nat × Nat) := [
  (573, 1631), (648, 1634)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y10_check. -/
theorem Z0Split54A0X0Y10_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y10_pairs. -/
theorem Z0Split54A0X0Y10_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk10,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y10Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk10_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk10
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk10_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · exact Z0Split54A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y11Certs : List (Nat × Nat) := [
  (178, 1712), (241, 1715)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y11_check. -/
theorem Z0Split54A0X0Y11_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y11Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y11_pairs. -/
theorem Z0Split54A0X0Y11_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk11,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y11Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk11_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk11
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk11_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · exact Z0Split54A0X0Y11_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y12Certs : List (Nat × Nat) := [
  (817, 1819), (1907, 1888)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y12_check. -/
theorem Z0Split54A0X0Y12_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y12Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y12_pairs. -/
theorem Z0Split54A0X0Y12_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk12,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y12Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk12_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk12
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk12_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · exact Z0Split54A0X0Y12_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y13Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y13_check. -/
theorem Z0Split54A0X0Y13_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y13Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y13_pairs. -/
theorem Z0Split54A0X0Y13_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk13,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y13Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk13_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk13
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk13_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · exact Z0Split54A0X0Y13_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y14Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y14_check. -/
theorem Z0Split54A0X0Y14_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y14Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y14_pairs. -/
theorem Z0Split54A0X0Y14_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk14,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y14Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk14_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk14
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk14_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · exact Z0Split54A0X0Y14_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y15Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y15_check. -/
theorem Z0Split54A0X0Y15_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y15Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y15_pairs. -/
theorem Z0Split54A0X0Y15_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk15,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y15Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk15_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk15
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk15_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · exact Z0Split54A0X0Y15_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y16Certs : List (Nat × Nat) := [
  (21, 2112), (757, 2178)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y16_check. -/
theorem Z0Split54A0X0Y16_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y16Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y16_pairs. -/
theorem Z0Split54A0X0Y16_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk16,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y16Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk16_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk16
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk16_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · exact Z0Split54A0X0Y16_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split54A0X0Y17Certs : List (Nat × Nat) := [
  (962, 2303), (1156, 2310)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y17_check. -/
theorem Z0Split54A0X0Y17_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y17Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0Y17_pairs. -/
theorem Z0Split54A0X0Y17_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk17,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z0M0LeftColumns Z0M0RightColumns) Z0Split54A0X0Y17Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk17_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks4S2048Chunk17
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk17_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · exact Z0Split54A0X0Y17_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split54A0X0_pairs. -/
theorem Z0Split54A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split54A0X0Y0_pairs x hx y hy hw
  · exact Z0Split54A0X0Y1_pairs x hx y hy hw
  · exact Z0Split54A0X0Y2_pairs x hx y hy hw
  · exact Z0Split54A0X0Y3_pairs x hx y hy hw
  · exact Z0Split54A0X0Y4_pairs x hx y hy hw
  · exact Z0Split54A0X0Y5_pairs x hx y hy hw
  · exact Z0Split54A0X0Y6_pairs x hx y hy hw
  · exact Z0Split54A0X0Y7_pairs x hx y hy hw
  · exact Z0Split54A0X0Y8_pairs x hx y hy hw
  · exact Z0Split54A0X0Y9_pairs x hx y hy hw
  · exact Z0Split54A0X0Y10_pairs x hx y hy hw
  · exact Z0Split54A0X0Y11_pairs x hx y hy hw
  · exact Z0Split54A0X0Y12_pairs x hx y hy hw
  · exact Z0Split54A0X0Y13_pairs x hx y hy hw
  · exact Z0Split54A0X0Y14_pairs x hx y hy hw
  · exact Z0Split54A0X0Y15_pairs x hx y hy hw
  · exact Z0Split54A0X0Y16_pairs x hx y hy hw
  · exact Z0Split54A0X0Y17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split55A0X0Y0Certs : List (Nat × Nat) := [
  (180, 242), (443, 410), (592, 506), (748, 582), (1315, 897),
  (1365, 932), (1640, 1079), (1826, 1174), (1930, 1232)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0Y0_check. -/
theorem Z0Split55A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split55A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0Y0_pairs. -/
theorem Z0Split55A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split55A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z0M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split55A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split55A0X0Y1Certs : List (Nat × Nat) := [
  (491, 1522), (561, 1552), (781, 1672), (967, 1773), (978, 1776),
  (1039, 1810), (1298, 1963), (1360, 1985), (1785, 2181), (1800, 2188),
  (1889, 2242)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0Y1_check. -/
theorem Z0Split55A0X0Y1_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split55A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0Y1_pairs. -/
theorem Z0Split55A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split55A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z0M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split55A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split55A0X0_pairs. -/
theorem Z0Split55A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split55A0X0Y0_pairs x hx y hy hw
  · exact Z0Split55A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split56A0X0Y0Certs : List (Nat × Nat) := [
  (39, 182), (112, 446), (172, 737), (195, 849), (223, 962),
  (239, 1042), (280, 1303), (310, 1471), (339, 1610), (394, 1990)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split56A0X0Y0_check. -/
theorem Z0Split56A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split56A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split56A0X0Y0_pairs. -/
theorem Z0Split56A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split56A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split56A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split56A0X0_pairs. -/
theorem Z0Split56A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split56A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split57A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0X0Y0_check. -/
theorem Z0Split57A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split57A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0X0Y0_pairs. -/
theorem Z0Split57A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split57A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split57A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0X0_pairs. -/
theorem Z0Split57A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split57A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split57A0_pairs. -/
theorem Z0Split57A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split57A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split58A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0X0Y0_check. -/
theorem Z0Split58A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split58A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0X0Y0_pairs. -/
theorem Z0Split58A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 8 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split58A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M0Left_eq
    · exact Z0M0Right_eq
    · intro x hx
      exact Z0M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split58A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0X0_pairs. -/
theorem Z0Split58A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 8 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split58A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split58A0_pairs. -/
theorem Z0Split58A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 8 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split58A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0X0Y0_check. -/
theorem Z0Split59A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0X0Y0_pairs. -/
theorem Z0Split59A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split59A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0X0_pairs. -/
theorem Z0Split59A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A0_pairs. -/
theorem Z0Split59A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 7 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1X0Y0_check. -/
theorem Z0Split59A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1X0Y0_pairs. -/
theorem Z0Split59A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split59A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1X0_pairs. -/
theorem Z0Split59A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A1_pairs. -/
theorem Z0Split59A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 7 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2X0Y0_check. -/
theorem Z0Split59A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2X0Y0_pairs. -/
theorem Z0Split59A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split59A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2X0_pairs. -/
theorem Z0Split59A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A2_pairs. -/
theorem Z0Split59A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 7 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split59A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3X0Y0_check. -/
theorem Z0Split59A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3X0Y0_pairs. -/
theorem Z0Split59A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split59A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split59A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3X0_pairs. -/
theorem Z0Split59A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split59A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split59A3_pairs. -/
theorem Z0Split59A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 7 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split59A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A0X0Y0Certs : List (Nat × Nat) := [
  (21, 0), (120, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0X0Y0_check. -/
theorem Z0Split60A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0X0Y0_pairs. -/
theorem Z0Split60A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split60A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0X0_pairs. -/
theorem Z0Split60A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A0_pairs. -/
theorem Z0Split60A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1X0Y0_check. -/
theorem Z0Split60A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1X0Y0_pairs. -/
theorem Z0Split60A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split60A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1X0_pairs. -/
theorem Z0Split60A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A1_pairs. -/
theorem Z0Split60A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2X0Y0_check. -/
theorem Z0Split60A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2X0Y0_pairs. -/
theorem Z0Split60A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split60A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2X0_pairs. -/
theorem Z0Split60A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A2_pairs. -/
theorem Z0Split60A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split60A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3X0Y0_check. -/
theorem Z0Split60A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3X0Y0_pairs. -/
theorem Z0Split60A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split60A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split60A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3X0_pairs. -/
theorem Z0Split60A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split60A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split60A3_pairs. -/
theorem Z0Split60A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split60A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A0X0Y0_check. -/
theorem Z0Split61A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A0X0Y0_pairs. -/
theorem Z0Split61A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split61A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A0X0_pairs. -/
theorem Z0Split61A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split61A1X0Y0Certs : List (Nat × Nat) := [
  (1958, 1999), (4173, 0), (7299, 2029), (9559, 2037)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A1X0Y0_check. -/
theorem Z0Split61A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A1X0Y0_pairs. -/
theorem Z0Split61A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split61A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A1X0_pairs. -/
theorem Z0Split61A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split61A2X0Y0Certs : List (Nat × Nat) := [
  (828, 2266), (1402, 0), (1878, 2231), (2594, 2211), (4589, 2280),
  (6420, 0), (7163, 2198), (9988, 0), (10005, 0), (11703, 0),
  (11833, 0), (12137, 0), (12279, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A2X0Y0_check. -/
theorem Z0Split61A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A2X0Y0_pairs. -/
theorem Z0Split61A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split61A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A2X0_pairs. -/
theorem Z0Split61A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split61A3X0Y0Certs : List (Nat × Nat) := [
  (587, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A3X0Y0_check. -/
theorem Z0Split61A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A3X0Y0_pairs. -/
theorem Z0Split61A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split61A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split61A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split61A3X0_pairs. -/
theorem Z0Split61A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split61A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y0Certs : List (Nat × Nat) := [
  (10041, 366), (10505, 448), (26064, 293), (28789, 455), (30511, 443),
  (40714, 305), (49819, 308), (53478, 310)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y0_check. -/
theorem Z0Split62A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y0_pairs. -/
theorem Z0Split62A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk0_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · exact Z0Split62A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y1Certs : List (Nat × Nat) := [
  (12388, 612), (27920, 565), (36947, 601)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y1_check. -/
theorem Z0Split62A0X0Y1_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y1_pairs. -/
theorem Z0Split62A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk1_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk1_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · exact Z0Split62A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y2Certs : List (Nat × Nat) := [
  (7399, 668), (7732, 703), (16541, 691), (17936, 653), (19520, 820),
  (20426, 724), (23126, 821), (29074, 697), (29729, 789), (30294, 822),
  (36182, 692), (38323, 753), (46461, 647), (46881, 687), (47144, 713),
  (51614, 815), (52520, 720)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y2_check. -/
theorem Z0Split62A0X0Y2_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y2_pairs. -/
theorem Z0Split62A0X0Y2_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y2Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk2_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk2
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk2_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · exact Z0Split62A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y3Certs : List (Nat × Nat) := [
  (2, 843), (26207, 902)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y3_check. -/
theorem Z0Split62A0X0Y3_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y3_pairs. -/
theorem Z0Split62A0X0Y3_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y3Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk3_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk3
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk3_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · exact Z0Split62A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y4Certs : List (Nat × Nat) := [
  (6876, 950), (13613, 967), (20237, 965), (28515, 982), (29485, 949),
  (29518, 956), (29976, 994), (33602, 969)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y4_check. -/
theorem Z0Split62A0X0Y4_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y4_pairs. -/
theorem Z0Split62A0X0Y4_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y4Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk4_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk4
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk4_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · exact Z0Split62A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y5Certs : List (Nat × Nat) := [
  (1863, 1072), (12939, 1091), (14260, 1080), (15483, 1047), (34593, 1095),
  (38244, 1119)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y5_check. -/
theorem Z0Split62A0X0Y5_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y5_pairs. -/
theorem Z0Split62A0X0Y5_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y5Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk5_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk5
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk5_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · exact Z0Split62A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y6Certs : List (Nat × Nat) := [
  (549, 1204), (5395, 1160), (6906, 1280), (7250, 1175), (9520, 1213),
  (19997, 1201), (20402, 1244), (20771, 1263), (27306, 1222), (27945, 1268),
  (28322, 1283), (31503, 1269), (46495, 1192), (46503, 1196), (48405, 1210),
  (52274, 1242)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y6_check. -/
theorem Z0Split62A0X0Y6_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y6_pairs. -/
theorem Z0Split62A0X0Y6_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y6Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk6_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk6
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk6_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · exact Z0Split62A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y7Certs : List (Nat × Nat) := [
  (2263, 1345), (8315, 1343), (16218, 1313), (19587, 1416), (32854, 1362),
  (37156, 1382), (37339, 1390), (45654, 1402), (45804, 1409), (52711, 1325)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y7_check. -/
theorem Z0Split62A0X0Y7_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y7_pairs. -/
theorem Z0Split62A0X0Y7_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y7Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk7_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk7
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk7_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · exact Z0Split62A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y8Certs : List (Nat × Nat) := [
  (4100, 1465), (34688, 1483), (43854, 1523), (54400, 1534)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y8_check. -/
theorem Z0Split62A0X0Y8_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y8_pairs. -/
theorem Z0Split62A0X0Y8_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk8,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y8Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk8_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk8
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk8_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · exact Z0Split62A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y9Certs : List (Nat × Nat) := [
  (5486, 1556), (7221, 1553)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y9_check. -/
theorem Z0Split62A0X0Y9_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y9_pairs. -/
theorem Z0Split62A0X0Y9_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk9,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y9Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk9_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk9
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk9_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · exact Z0Split62A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y10Certs : List (Nat × Nat) := [
  (9174, 1661), (9700, 1686), (19006, 1640), (30021, 1691), (31607, 1673),
  (32838, 1617), (42361, 1704), (54496, 1700)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y10_check. -/
theorem Z0Split62A0X0Y10_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y10_pairs. -/
theorem Z0Split62A0X0Y10_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk10,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y10Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk10_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk10
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk10_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · exact Z0Split62A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y11Certs : List (Nat × Nat) := [
  (2271, 1727), (11285, 1723)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y11_check. -/
theorem Z0Split62A0X0Y11_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk11
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y11Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y11_pairs. -/
theorem Z0Split62A0X0Y11_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk11,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk11
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y11Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk11_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk11
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk11_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · exact Z0Split62A0X0Y11_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y12Certs : List (Nat × Nat) := [
  (5575, 1866), (11385, 1840), (11444, 1846), (11469, 1853), (14620, 1786),
  (18913, 1812), (21992, 1877), (23495, 1837), (35739, 1849), (35886, 1863),
  (43110, 1804), (43397, 1824), (44423, 1889), (47370, 1820), (51980, 1857),
  (54819, 1771), (60329, 1873)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y12_check. -/
theorem Z0Split62A0X0Y12_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk12
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y12Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y12_pairs. -/
theorem Z0Split62A0X0Y12_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk12,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk12
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y12Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk12_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk12
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk12_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · exact Z0Split62A0X0Y12_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y13Certs : List (Nat × Nat) := [
  (7017, 1922), (15866, 1912), (19576, 1917)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y13_check. -/
theorem Z0Split62A0X0Y13_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk13
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y13Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y13_pairs. -/
theorem Z0Split62A0X0Y13_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk13,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk13
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y13Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk13_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk13
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk13_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · exact Z0Split62A0X0Y13_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y14Certs : List (Nat × Nat) := [
  (2290, 1978), (10685, 1992), (12502, 1980), (25316, 2014), (39118, 1997),
  (47514, 2012), (49381, 2008), (55402, 2005)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y14_check. -/
theorem Z0Split62A0X0Y14_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk14
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y14Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y14_pairs. -/
theorem Z0Split62A0X0Y14_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk14,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk14
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y14Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk14_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk14
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk14_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · exact Z0Split62A0X0Y14_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y15Certs : List (Nat × Nat) := [
  (7188, 2074), (9860, 2083), (20090, 2043), (20739, 2063), (29133, 2053),
  (30763, 2064)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y15_check. -/
theorem Z0Split62A0X0Y15_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk15
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y15Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y15_pairs. -/
theorem Z0Split62A0X0Y15_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk15,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk15
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y15Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk15_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk15
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk15_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · exact Z0Split62A0X0Y15_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y16Certs : List (Nat × Nat) := [
  (2976, 2189), (3007, 2197), (3688, 2234), (18953, 2176), (20497, 2145),
  (20600, 2154), (27639, 2206), (28047, 2238), (32203, 2244), (46574, 2113),
  (48477, 2248), (54674, 2114), (57278, 2168), (59414, 2174)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y16_check. -/
theorem Z0Split62A0X0Y16_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk16
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y16Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y16_pairs. -/
theorem Z0Split62A0X0Y16_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk16,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk16
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y16Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk16_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk16
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk16_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · exact Z0Split62A0X0Y16_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split62A0X0Y17Certs : List (Nat × Nat) := [
  (2802, 2311), (7476, 2302), (10135, 2269), (16817, 2274), (16871, 2281),
  (18702, 2291), (21519, 2265), (26672, 2286), (28178, 2271), (39118, 2324),
  (45325, 2315)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y17_check. -/
theorem Z0Split62A0X0Y17_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk17
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y17Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0Y17_pairs. -/
theorem Z0Split62A0X0Y17_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks4S2048Chunk17,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks1S256Chunk0 masks4S2048Chunk17
      Z0M0LeftColumns Z0M0RightColumns) Z0Split62A0X0Y17Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks4S2048Chunk17_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks4S2048Chunk17
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks4S2048Chunk17_bound
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
      exact Z0M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · exact Z0Split62A0X0Y17_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split62A0X0_pairs. -/
theorem Z0Split62A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0Split62A0X0Y0_pairs x hx y hy hw
  · exact Z0Split62A0X0Y1_pairs x hx y hy hw
  · exact Z0Split62A0X0Y2_pairs x hx y hy hw
  · exact Z0Split62A0X0Y3_pairs x hx y hy hw
  · exact Z0Split62A0X0Y4_pairs x hx y hy hw
  · exact Z0Split62A0X0Y5_pairs x hx y hy hw
  · exact Z0Split62A0X0Y6_pairs x hx y hy hw
  · exact Z0Split62A0X0Y7_pairs x hx y hy hw
  · exact Z0Split62A0X0Y8_pairs x hx y hy hw
  · exact Z0Split62A0X0Y9_pairs x hx y hy hw
  · exact Z0Split62A0X0Y10_pairs x hx y hy hw
  · exact Z0Split62A0X0Y11_pairs x hx y hy hw
  · exact Z0Split62A0X0Y12_pairs x hx y hy hw
  · exact Z0Split62A0X0Y13_pairs x hx y hy hw
  · exact Z0Split62A0X0Y14_pairs x hx y hy hw
  · exact Z0Split62A0X0Y15_pairs x hx y hy hw
  · exact Z0Split62A0X0Y16_pairs x hx y hy hw
  · exact Z0Split62A0X0Y17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split63A0X0Y0Certs : List (Nat × Nat) := [
  (1964, 1256), (3948, 1228), (10787, 532), (11458, 923), (16451, 292),
  (18128, 1239), (20340, 187), (20560, 347), (21996, 1123), (23196, 696),
  (23507, 875), (25320, 782), (29055, 567), (29264, 690), (30641, 306),
  (31323, 714), (32909, 465), (33456, 793), (35337, 693), (35874, 988),
  (41888, 963), (42363, 1198), (43468, 717), (44352, 1182), (44411, 1217),
  (45358, 641), (46020, 999), (46733, 243), (47973, 972), (48325, 1147),
  (50782, 244), (51571, 742), (52780, 224), (53079, 428), (55238, 505),
  (55398, 584), (55790, 842), (57424, 585), (59094, 393), (60333, 1077),
  (60629, 1235)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0Y0_check. -/
theorem Z0Split63A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split63A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0Y0_pairs. -/
theorem Z0Split63A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split63A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z0M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split63A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split63A0X0Y1Certs : List (Nat × Nat) := [
  (3107, 1828), (3192, 1881), (5280, 1904), (9046, 1742), (10027, 2241),
  (10131, 2299), (11455, 1952), (14237, 2316), (16347, 1340), (19282, 1770),
  (19971, 2111), (20031, 2146), (23174, 1670), (23402, 1788), (23723, 1976),
  (29558, 1817), (32312, 2172), (33219, 1604), (35046, 1507), (35096, 1520),
  (36454, 2208), (36798, 1385), (42351, 2098), (45000, 1410), (48125, 1962),
  (48380, 2051), (52024, 1860), (53215, 1456), (55892, 1757), (56254, 1956),
  (57027, 1312), (58810, 2195), (59339, 1464), (60749, 2144)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0Y1_check. -/
theorem Z0Split63A0X0Y1_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split63A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0Y1_pairs. -/
theorem Z0Split63A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split63A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z0M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split63A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split63A0X0_pairs. -/
theorem Z0Split63A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split63A0X0Y0_pairs x hx y hy hw
  · exact Z0Split63A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

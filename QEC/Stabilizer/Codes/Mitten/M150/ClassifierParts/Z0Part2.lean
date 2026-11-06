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
def Z0Split32A0X0Y0Certs : List (Nat × Nat) := [
  (4902, 464), (7623, 997), (10005, 22), (11753, 67), (12657, 186)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split32A0X0Y0_check. -/
theorem Z0Split32A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split32A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split32A0X0Y0_pairs. -/
theorem Z0Split32A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split32A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split32A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split32A0X0_pairs. -/
theorem Z0Split32A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split32A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split33A0X0Y0Certs : List (Nat × Nat) := [
  (59, 2092), (131, 231), (287, 535), (473, 1131), (657, 1731)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0X0Y0_check. -/
theorem Z0Split33A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split33A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0X0Y0_pairs. -/
theorem Z0Split33A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split33A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split33A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0X0_pairs. -/
theorem Z0Split33A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split33A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split33A0_pairs. -/
theorem Z0Split33A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split33A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split34A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0X0Y0_check. -/
theorem Z0Split34A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split34A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0X0Y0_pairs. -/
theorem Z0Split34A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split34A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z0Split34A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0X0_pairs. -/
theorem Z0Split34A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split34A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split34A0_pairs. -/
theorem Z0Split34A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split34A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0X0Y0_check. -/
theorem Z0Split35A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0X0Y0_pairs. -/
theorem Z0Split35A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0X0_pairs. -/
theorem Z0Split35A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A0_pairs. -/
theorem Z0Split35A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1X0Y0_check. -/
theorem Z0Split35A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1X0Y0_pairs. -/
theorem Z0Split35A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1X0_pairs. -/
theorem Z0Split35A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A1_pairs. -/
theorem Z0Split35A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2X0Y0_check. -/
theorem Z0Split35A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2X0Y0_pairs. -/
theorem Z0Split35A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2X0_pairs. -/
theorem Z0Split35A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A2_pairs. -/
theorem Z0Split35A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split35A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3X0Y0_check. -/
theorem Z0Split35A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3X0Y0_pairs. -/
theorem Z0Split35A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split35A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split35A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3X0_pairs. -/
theorem Z0Split35A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split35A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split35A3_pairs. -/
theorem Z0Split35A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split35A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A0X0Y0Certs : List (Nat × Nat) := [
  (3030, 0), (3492, 463), (3998, 0), (6828, 996), (7363, 194),
  (7620, 1229), (9174, 1015), (10369, 475), (10652, 1748), (11643, 1548),
  (11698, 0), (11912, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0X0Y0_check. -/
theorem Z0Split36A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0X0Y0_pairs. -/
theorem Z0Split36A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0X0_pairs. -/
theorem Z0Split36A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A0_pairs. -/
theorem Z0Split36A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A1X0Y0Certs : List (Nat × Nat) := [
  (3847, 1945)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1X0Y0_check. -/
theorem Z0Split36A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1X0Y0_pairs. -/
theorem Z0Split36A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1X0_pairs. -/
theorem Z0Split36A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A1_pairs. -/
theorem Z0Split36A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A2X0Y0Certs : List (Nat × Nat) := [
  (12456, 2125)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2X0Y0_check. -/
theorem Z0Split36A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2X0Y0_pairs. -/
theorem Z0Split36A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2X0_pairs. -/
theorem Z0Split36A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A2_pairs. -/
theorem Z0Split36A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split36A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3X0Y0_check. -/
theorem Z0Split36A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3X0Y0_pairs. -/
theorem Z0Split36A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split36A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split36A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3X0_pairs. -/
theorem Z0Split36A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split36A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split36A3_pairs. -/
theorem Z0Split36A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split36A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split37A0X0Y0Certs : List (Nat × Nat) := [
  (12681, 273), (41480, 632), (86580, 96)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X0Y0_check. -/
theorem Z0Split37A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X0Y0_pairs. -/
theorem Z0Split37A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split37A0X1Y0Certs : List (Nat × Nat) := [
  (27038, 276), (63669, 644)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X1Y0_check. -/
theorem Z0Split37A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split37A0X1Y0_pairs. -/
theorem Z0Split37A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split37A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split38A0X0Y0Certs : List (Nat × Nat) := [
  (978, 616), (3000, 1), (3934, 58), (6152, 25), (7449, 167),
  (9636, 88), (10455, 415), (10701, 906), (11382, 267), (12481, 14)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0X0Y0_check. -/
theorem Z0Split38A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split38A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0X0Y0_pairs. -/
theorem Z0Split38A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split38A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split38A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0X0_pairs. -/
theorem Z0Split38A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split38A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split38A0_pairs. -/
theorem Z0Split38A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split38A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split39A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0X0Y0_check. -/
theorem Z0Split39A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split39A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0X0Y0_pairs. -/
theorem Z0Split39A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split39A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split39A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0X0_pairs. -/
theorem Z0Split39A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split39A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split39A0_pairs. -/
theorem Z0Split39A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split39A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split40A0X0Y0Certs : List (Nat × Nat) := [
  (250, 286), (514, 461), (897, 673), (913, 680), (987, 754),
  (990, 759), (1206, 866), (1455, 980), (1475, 993), (1581, 1052),
  (1586, 1057), (1877, 1195)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0Y0_check. -/
theorem Z0Split40A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split40A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0Y0_pairs. -/
theorem Z0Split40A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split40A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z0M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z0Split40A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split40A0X0Y1Certs : List (Nat × Nat) := [
  (73, 1346), (80, 1353), (198, 1406), (362, 1487), (370, 1490),
  (431, 1506), (691, 1623), (700, 1630), (840, 1699), (1032, 1805),
  (1042, 1811), (1115, 1851), (1267, 1949), (1437, 2017), (1449, 2020),
  (1667, 2124), (1878, 2235), (1893, 2243)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0Y1_check. -/
theorem Z0Split40A0X0Y1_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split40A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0Y1_pairs. -/
theorem Z0Split40A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split40A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z0M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z0Split40A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split40A0X0_pairs. -/
theorem Z0Split40A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split40A0X0Y0_pairs x hx y hy hw
  · exact Z0Split40A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split41A0X0Y0Certs : List (Nat × Nat) := [
  (520, 342), (1924, 784), (4210, 1392), (6804, 1300), (9159, 124)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split41A0X0Y0_check. -/
theorem Z0Split41A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split41A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split41A0X0Y0_pairs. -/
theorem Z0Split41A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split41A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split41A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split41A0X0_pairs. -/
theorem Z0Split41A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split41A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split42A0X0Y0Certs : List (Nat × Nat) := [
  (1066, 476), (3142, 1017), (6296, 1561), (9725, 74), (11440, 199)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0X0Y0_check. -/
theorem Z0Split42A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split42A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0X0Y0_pairs. -/
theorem Z0Split42A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split42A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split42A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0X0_pairs. -/
theorem Z0Split42A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split42A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split42A0_pairs. -/
theorem Z0Split42A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split42A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split43A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X0Y0_check. -/
theorem Z0Split43A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split43A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X0Y0_pairs. -/
theorem Z0Split43A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split43A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split43A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X0_pairs. -/
theorem Z0Split43A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split43A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split43A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X1Y0_check. -/
theorem Z0Split43A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split43A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X1Y0_pairs. -/
theorem Z0Split43A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split43A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split43A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0X1_pairs. -/
theorem Z0Split43A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split43A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split43A0_pairs. -/
theorem Z0Split43A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split43A0X0_pairs x hx y hy hw
  · exact Z0Split43A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split44A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split44A0X0Y0_check. -/
theorem Z0Split44A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split44A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split44A0X0Y0_pairs. -/
theorem Z0Split44A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split44A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
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
      exact Z0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z0Split44A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split44A0X0_pairs. -/
theorem Z0Split44A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split44A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split45A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0X0Y0_check. -/
theorem Z0Split45A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split45A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0X0Y0_pairs. -/
theorem Z0Split45A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split45A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
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
      exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split45A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0X0_pairs. -/
theorem Z0Split45A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split45A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split45A0_pairs. -/
theorem Z0Split45A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split45A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split46A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0X0Y0_check. -/
theorem Z0Split46A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split46A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0X0Y0_pairs. -/
theorem Z0Split46A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split46A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
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
      exact Z0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split46A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0X0_pairs. -/
theorem Z0Split46A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split46A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split46A0_pairs. -/
theorem Z0Split46A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split46A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split47A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0X0Y0_check. -/
theorem Z0Split47A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split47A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0X0Y0_pairs. -/
theorem Z0Split47A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split47A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
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
      exact Z0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z0Split47A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0X0_pairs. -/
theorem Z0Split47A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split47A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split47A0_pairs. -/
theorem Z0Split47A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 5 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split47A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

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
def Z0Split16A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split16A0X0Y0_check. -/
theorem Z0Split16A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 2
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split16A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split16A0X0Y0_pairs. -/
theorem Z0Split16A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 2
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split16A0X0Y0Certs
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
  · exact Z0Split16A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split16A0X0_pairs. -/
theorem Z0Split16A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split16A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split17A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0X0Y0_check. -/
theorem Z0Split17A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split17A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0X0Y0_pairs. -/
theorem Z0Split17A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split17A0X0Y0Certs
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
  · exact Z0Split17A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0X0_pairs. -/
theorem Z0Split17A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split17A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split17A0_pairs. -/
theorem Z0Split17A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 2 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split17A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split18A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0X0Y0_check. -/
theorem Z0Split18A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split18A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0X0Y0_pairs. -/
theorem Z0Split18A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split18A0X0Y0Certs
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
  · exact Z0Split18A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0X0_pairs. -/
theorem Z0Split18A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split18A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split18A0_pairs. -/
theorem Z0Split18A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 2 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split18A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split19A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0X0Y0_check. -/
theorem Z0Split19A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split19A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0X0Y0_pairs. -/
theorem Z0Split19A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split19A0X0Y0Certs
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
  · exact Z0Split19A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0X0_pairs. -/
theorem Z0Split19A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split19A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split19A0_pairs. -/
theorem Z0Split19A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split19A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split20A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0X0Y0_check. -/
theorem Z0Split20A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split20A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0X0Y0_pairs. -/
theorem Z0Split20A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split20A0X0Y0Certs
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
  · exact Z0Split20A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0X0_pairs. -/
theorem Z0Split20A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split20A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split20A0_pairs. -/
theorem Z0Split20A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split20A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split21A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0X0Y0_check. -/
theorem Z0Split21A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split21A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0X0Y0_pairs. -/
theorem Z0Split21A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split21A0X0Y0Certs
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
  · exact Z0Split21A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0X0_pairs. -/
theorem Z0Split21A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split21A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split21A0_pairs. -/
theorem Z0Split21A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 4 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split21A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0X0Y0_check. -/
theorem Z0Split22A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0X0Y0_pairs. -/
theorem Z0Split22A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A0X0Y0Certs
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
  · exact Z0Split22A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0X0_pairs. -/
theorem Z0Split22A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A0_pairs. -/
theorem Z0Split22A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1X0Y0_check. -/
theorem Z0Split22A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1X0Y0_pairs. -/
theorem Z0Split22A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A1X0Y0Certs
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
  · exact Z0Split22A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1X0_pairs. -/
theorem Z0Split22A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A1_pairs. -/
theorem Z0Split22A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2X0Y0_check. -/
theorem Z0Split22A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2X0Y0_pairs. -/
theorem Z0Split22A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A2X0Y0Certs
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
  · exact Z0Split22A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2X0_pairs. -/
theorem Z0Split22A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A2_pairs. -/
theorem Z0Split22A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split22A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3X0Y0_check. -/
theorem Z0Split22A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3X0Y0_pairs. -/
theorem Z0Split22A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split22A3X0Y0Certs
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
  · exact Z0Split22A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3X0_pairs. -/
theorem Z0Split22A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split22A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split22A3_pairs. -/
theorem Z0Split22A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split22A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0X0Y0_check. -/
theorem Z0Split23A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0X0Y0_pairs. -/
theorem Z0Split23A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A0X0Y0Certs
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
  · exact Z0Split23A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0X0_pairs. -/
theorem Z0Split23A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A0_pairs. -/
theorem Z0Split23A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1X0Y0_check. -/
theorem Z0Split23A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1X0Y0_pairs. -/
theorem Z0Split23A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A1X0Y0Certs
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
  · exact Z0Split23A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1X0_pairs. -/
theorem Z0Split23A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A1_pairs. -/
theorem Z0Split23A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2X0Y0_check. -/
theorem Z0Split23A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2X0Y0_pairs. -/
theorem Z0Split23A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A2X0Y0Certs
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
  · exact Z0Split23A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2X0_pairs. -/
theorem Z0Split23A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A2_pairs. -/
theorem Z0Split23A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split23A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3X0Y0_check. -/
theorem Z0Split23A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3X0Y0_pairs. -/
theorem Z0Split23A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split23A3X0Y0Certs
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
  · exact Z0Split23A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3X0_pairs. -/
theorem Z0Split23A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split23A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split23A3_pairs. -/
theorem Z0Split23A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split23A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A0X0Y0_check. -/
theorem Z0Split24A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A0X0Y0_pairs. -/
theorem Z0Split24A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A0X0Y0Certs
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
  · exact Z0Split24A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A0X0_pairs. -/
theorem Z0Split24A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A1X0Y0_check. -/
theorem Z0Split24A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A1X0Y0_pairs. -/
theorem Z0Split24A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A1X0Y0Certs
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
  · exact Z0Split24A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A1X0_pairs. -/
theorem Z0Split24A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A2X0Y0_check. -/
theorem Z0Split24A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A2X0Y0_pairs. -/
theorem Z0Split24A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A2X0Y0Certs
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
  · exact Z0Split24A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A2X0_pairs. -/
theorem Z0Split24A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split24A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A3X0Y0_check. -/
theorem Z0Split24A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A3X0Y0_pairs. -/
theorem Z0Split24A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split24A3X0Y0Certs
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
  · exact Z0Split24A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split24A3X0_pairs. -/
theorem Z0Split24A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split24A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split25A0X0Y0Certs : List (Nat × Nat) := [
  (336, 356), (408, 395), (584, 500), (741, 577), (893, 669),
  (952, 708), (1099, 805), (1147, 846), (1259, 877), (1422, 973),
  (1443, 977), (1625, 1069), (1772, 1146), (1919, 1223)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0Y0_check. -/
theorem Z0Split25A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split25A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0Y0_pairs. -/
theorem Z0Split25A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split25A0X0Y0Certs
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
  · exact Z0Split25A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split25A0X0Y1Certs : List (Nat × Nat) := [
  (48, 1331), (176, 1396), (247, 1431), (316, 1468), (506, 1527),
  (602, 1588), (760, 1658), (810, 1685), (918, 1756), (1172, 1890),
  (1284, 1957), (1366, 1986), (1553, 2052), (1687, 2134), (1702, 2143),
  (1981, 2297)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0Y1_check. -/
theorem Z0Split25A0X0Y1_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split25A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0Y1_pairs. -/
theorem Z0Split25A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split25A0X0Y1Certs
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
  · exact Z0Split25A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split25A0X0_pairs. -/
theorem Z0Split25A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z0Split25A0X0Y0_pairs x hx y hy hw
  · exact Z0Split25A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split26A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split26A0X0Y0_check. -/
theorem Z0Split26A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split26A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split26A0X0Y0_pairs. -/
theorem Z0Split26A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split26A0X0Y0Certs
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
  · exact Z0Split26A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split26A0X0_pairs. -/
theorem Z0Split26A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split26A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split27A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0X0Y0_check. -/
theorem Z0Split27A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split27A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0X0Y0_pairs. -/
theorem Z0Split27A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split27A0X0Y0Certs
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
  · exact Z0Split27A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0X0_pairs. -/
theorem Z0Split27A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split27A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split27A0_pairs. -/
theorem Z0Split27A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split27A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split28A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0X0Y0_check. -/
theorem Z0Split28A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split28A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0X0Y0_pairs. -/
theorem Z0Split28A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split28A0X0Y0Certs
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
  · exact Z0Split28A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0X0_pairs. -/
theorem Z0Split28A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split28A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split28A0_pairs. -/
theorem Z0Split28A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split28A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0X0Y0_check. -/
theorem Z0Split29A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0X0Y0_pairs. -/
theorem Z0Split29A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A0X0Y0Certs
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
  · exact Z0Split29A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0X0_pairs. -/
theorem Z0Split29A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A0_pairs. -/
theorem Z0Split29A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1X0Y0_check. -/
theorem Z0Split29A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1X0Y0_pairs. -/
theorem Z0Split29A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A1X0Y0Certs
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
  · exact Z0Split29A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1X0_pairs. -/
theorem Z0Split29A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A1_pairs. -/
theorem Z0Split29A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2X0Y0_check. -/
theorem Z0Split29A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2X0Y0_pairs. -/
theorem Z0Split29A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A2X0Y0Certs
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
  · exact Z0Split29A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2X0_pairs. -/
theorem Z0Split29A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A2_pairs. -/
theorem Z0Split29A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split29A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3X0Y0_check. -/
theorem Z0Split29A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3X0Y0_pairs. -/
theorem Z0Split29A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split29A3X0Y0Certs
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
  · exact Z0Split29A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3X0_pairs. -/
theorem Z0Split29A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split29A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split29A3_pairs. -/
theorem Z0Split29A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split29A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A0X0Y0Certs : List (Nat × Nat) := [
  (283, 992), (469, 1191), (654, 1844)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0X0Y0_check. -/
theorem Z0Split30A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0X0Y0_pairs. -/
theorem Z0Split30A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A0X0Y0Certs
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
  · exact Z0Split30A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0X0_pairs. -/
theorem Z0Split30A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A0_pairs. -/
theorem Z0Split30A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A1X0Y0Certs : List (Nat × Nat) := [
  (127, 1987)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1X0Y0_check. -/
theorem Z0Split30A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1X0Y0_pairs. -/
theorem Z0Split30A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A1X0Y0Certs
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
  · exact Z0Split30A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1X0_pairs. -/
theorem Z0Split30A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A1_pairs. -/
theorem Z0Split30A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A2X0Y0Certs : List (Nat × Nat) := [
  (33, 2279)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2X0Y0_check. -/
theorem Z0Split30A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2X0Y0_pairs. -/
theorem Z0Split30A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A2X0Y0Certs
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
  · exact Z0Split30A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2X0_pairs. -/
theorem Z0Split30A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A2_pairs. -/
theorem Z0Split30A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split30A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3X0Y0_check. -/
theorem Z0Split30A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3X0Y0_pairs. -/
theorem Z0Split30A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split30A3X0Y0Certs
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
  · exact Z0Split30A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3X0_pairs. -/
theorem Z0Split30A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split30A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split30A3_pairs. -/
theorem Z0Split30A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split30A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A0X0Y0Certs : List (Nat × Nat) := [
  (1800, 0), (2008, 252), (3042, 0), (4287, 604), (4795, 1225),
  (6932, 1271), (7442, 1892), (9194, 1830), (10495, 0), (12958, 578)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A0X0Y0_check. -/
theorem Z0Split31A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A0X0Y0_pairs. -/
theorem Z0Split31A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A0X0Y0Certs
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
  · exact Z0Split31A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A0X0_pairs. -/
theorem Z0Split31A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 3 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A1X0Y0_check. -/
theorem Z0Split31A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A1X0Y0_pairs. -/
theorem Z0Split31A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A1X0Y0Certs
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
  · exact Z0Split31A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A1X0_pairs. -/
theorem Z0Split31A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 3 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A2X0Y0Certs : List (Nat × Nat) := [
  (580, 2253), (2006, 0), (10131, 2298), (11988, 2135)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A2X0Y0_check. -/
theorem Z0Split31A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A2X0Y0_pairs. -/
theorem Z0Split31A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A2X0Y0Certs
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
  · exact Z0Split31A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A2X0_pairs. -/
theorem Z0Split31A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 3 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split31A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A3X0Y0_check. -/
theorem Z0Split31A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A3X0Y0_pairs. -/
theorem Z0Split31A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split31A3X0Y0Certs
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
  · exact Z0Split31A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split31A3X0_pairs. -/
theorem Z0Split31A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 3 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split31A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
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

end Quantum.Stabilizer.Homological.LP.M150

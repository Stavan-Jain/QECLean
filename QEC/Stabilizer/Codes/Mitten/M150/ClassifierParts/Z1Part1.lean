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
def Z1Split16A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0X0Y0_check. -/
theorem Z1Split16A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 2
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split16A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0X0Y0_pairs. -/
theorem Z1Split16A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 2
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split16A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split16A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0X0_pairs. -/
theorem Z1Split16A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split16A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split16A0_pairs. -/
theorem Z1Split16A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split16A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split16_check. -/
theorem Z1Split16_check : checkSplit m4TZ1 (2, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split16A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split17A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0X0Y0_check. -/
theorem Z1Split17A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split17A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0X0Y0_pairs. -/
theorem Z1Split17A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 2
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split17A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split17A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0X0_pairs. -/
theorem Z1Split17A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split17A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split17A0_pairs. -/
theorem Z1Split17A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 2 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split17A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split17_check. -/
theorem Z1Split17_check : checkSplit m4TZ1 (2, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split17A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split18A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0X0Y0_check. -/
theorem Z1Split18A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split18A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0X0Y0_pairs. -/
theorem Z1Split18A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 2
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split18A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split18A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0X0_pairs. -/
theorem Z1Split18A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split18A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split18A0_pairs. -/
theorem Z1Split18A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split18A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split18_check. -/
theorem Z1Split18_check : checkSplit m4TZ1 (2, 2, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split18A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split19A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0X0Y0_check. -/
theorem Z1Split19A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split19A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0X0Y0_pairs. -/
theorem Z1Split19A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split19A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split19A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0X0_pairs. -/
theorem Z1Split19A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split19A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split19A0_pairs. -/
theorem Z1Split19A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split19A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split19_check. -/
theorem Z1Split19_check : checkSplit m4TZ1 (3, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split19A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split20A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0X0Y0_check. -/
theorem Z1Split20A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split20A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0X0Y0_pairs. -/
theorem Z1Split20A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split20A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split20A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0X0_pairs. -/
theorem Z1Split20A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split20A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split20A0_pairs. -/
theorem Z1Split20A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split20A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split20_check. -/
theorem Z1Split20_check : checkSplit m4TZ1 (3, 1, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split20A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split21A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0X0Y0_check. -/
theorem Z1Split21A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split21A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0X0Y0_pairs. -/
theorem Z1Split21A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split21A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split21A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0X0_pairs. -/
theorem Z1Split21A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split21A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split21A0_pairs. -/
theorem Z1Split21A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split21A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split21_check. -/
theorem Z1Split21_check : checkSplit m4TZ1 (4, 0, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split21A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split22A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0X0Y0_check. -/
theorem Z1Split22A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split22A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0X0Y0_pairs. -/
theorem Z1Split22A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split22A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split22A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0X0_pairs. -/
theorem Z1Split22A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split22A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split22A0_pairs. -/
theorem Z1Split22A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split22A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split22_check. -/
theorem Z1Split22_check : checkSplit m4TZ1 (0, 0, 6, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split22A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split23A0X0Y0Certs : List (Nat × Nat) := [
  (0, 2442), (2, 3137), (6, 2457), (11, 2521), (12, 3035),
  (17, 3215), (18, 1577), (23, 3120), (27, 2471), (29, 3126)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0X0Y0_check. -/
theorem Z1Split23A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split23A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0X0Y0_pairs. -/
theorem Z1Split23A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split23A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split23A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0X0_pairs. -/
theorem Z1Split23A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split23A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split23A0_pairs. -/
theorem Z1Split23A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split23A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split23_check. -/
theorem Z1Split23_check : checkSplit m4TZ1 (0, 1, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split23A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split24A0X0Y0Certs : List (Nat × Nat) := [
  (15, 878), (57, 3206), (66, 3184), (68, 1586), (136, 3057),
  (142, 3031), (155, 3006), (159, 2505), (164, 2462), (255, 822),
  (264, 3180), (265, 1555), (357, 707), (362, 1590), (368, 2989),
  (369, 2527), (406, 3222), (418, 1516), (423, 2534), (429, 742)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0X0Y0_check. -/
theorem Z1Split24A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split24A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0X0Y0_pairs. -/
theorem Z1Split24A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split24A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split24A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0X0_pairs. -/
theorem Z1Split24A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split24A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split24A0_pairs. -/
theorem Z1Split24A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split24A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split24_check. -/
theorem Z1Split24_check : checkSplit m4TZ1 (0, 2, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split24A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split25A0X0Y0Certs : List (Nat × Nat) := [
  (275, 357), (277, 358), (336, 421), (408, 476), (584, 610),
  (741, 727), (893, 841), (952, 866), (954, 868), (958, 870),
  (1099, 982), (1147, 1017), (1259, 1086), (1422, 1224), (1443, 1241),
  (1625, 1356), (1772, 1469), (1786, 1479), (1832, 1503), (1837, 1509),
  (1919, 1560), (1935, 1573)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0Y0_check. -/
theorem Z1Split25A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split25A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0Y0_pairs. -/
theorem Z1Split25A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split25A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z1Split25A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split25A0X0Y1Certs : List (Nat × Nat) := [
  (48, 1672), (176, 1744), (247, 1819), (316, 1870), (506, 1980),
  (602, 2115), (760, 2210), (810, 2246), (918, 2370), (956, 2383),
  (962, 2385), (969, 2395), (1037, 2429), (1049, 2438), (1056, 2450),
  (1172, 2533), (1284, 2613), (1366, 2665), (1553, 2796), (1645, 2962),
  (1687, 2985), (1702, 3000), (1768, 3027), (1778, 3033), (1789, 3047),
  (1885, 3108), (1901, 3129), (1981, 3178)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0Y1_check. -/
theorem Z1Split25A0X0Y1_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split25A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0Y1_pairs. -/
theorem Z1Split25A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split25A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z1Split25A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0X0_pairs. -/
theorem Z1Split25A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split25A0X0Y0_pairs x hx y hy hw
  · exact Z1Split25A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split25A0_pairs. -/
theorem Z1Split25A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split25A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split25_check. -/
theorem Z1Split25_check : checkSplit m4TZ1 (0, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split25A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split26A0X0Y0Certs : List (Nat × Nat) := [
  (1, 36), (15, 103), (17, 107), (66, 324), (68, 329),
  (72, 342), (147, 722), (153, 788), (155, 790), (159, 800),
  (165, 835), (264, 1500), (270, 1544), (362, 2381), (368, 2428),
  (374, 2501), (417, 2981), (423, 3025), (429, 3106), (433, 3176)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0X0Y0_check. -/
theorem Z1Split26A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split26A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0X0Y0_pairs. -/
theorem Z1Split26A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split26A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split26A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0X0_pairs. -/
theorem Z1Split26A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split26A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split26A0_pairs. -/
theorem Z1Split26A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split26A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split26_check. -/
theorem Z1Split26_check : checkSplit m4TZ1 (0, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split26A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split27A0X0Y0Certs : List (Nat × Nat) := [
  (0, 13), (2, 34), (6, 101), (11, 270), (12, 323),
  (17, 682), (18, 780), (23, 1448), (27, 2338), (29, 2934)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0X0Y0_check. -/
theorem Z1Split27A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split27A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0X0Y0_pairs. -/
theorem Z1Split27A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split27A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split27A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0X0_pairs. -/
theorem Z1Split27A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split27A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split27A0_pairs. -/
theorem Z1Split27A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split27A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split27_check. -/
theorem Z1Split27_check : checkSplit m4TZ1 (0, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split27A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split28A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0X0Y0_check. -/
theorem Z1Split28A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split28A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0X0Y0_pairs. -/
theorem Z1Split28A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split28A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split28A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0X0_pairs. -/
theorem Z1Split28A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split28A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split28A0_pairs. -/
theorem Z1Split28A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split28A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split28_check. -/
theorem Z1Split28_check : checkSplit m4TZ1 (0, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split28A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split29A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0X0Y0_check. -/
theorem Z1Split29A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split29A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0X0Y0_pairs. -/
theorem Z1Split29A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split29A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split29A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0X0_pairs. -/
theorem Z1Split29A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split29A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split29A0_pairs. -/
theorem Z1Split29A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split29A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split29_check. -/
theorem Z1Split29_check : checkSplit m4TZ1 (1, 0, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split29A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split30A0X0Y0Certs : List (Nat × Nat) := [
  (15, 2035), (41, 2195), (81, 2909), (90, 2616), (137, 1528),
  (181, 2615), (212, 497), (293, 2484), (349, 2025), (364, 496),
  (396, 1126), (477, 3158), (534, 2893), (549, 1122), (582, 2039),
  (659, 2879), (693, 2124), (738, 2895), (817, 493), (883, 1116)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0X0Y0_check. -/
theorem Z1Split30A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split30A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0X0Y0_pairs. -/
theorem Z1Split30A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split30A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split30A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0X0_pairs. -/
theorem Z1Split30A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split30A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split30A0_pairs. -/
theorem Z1Split30A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split30A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split30_check. -/
theorem Z1Split30_check : checkSplit m4TZ1 (1, 1, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split30A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split31A0X0Y0Certs : List (Nat × Nat) := [
  (181, 249), (326, 2279), (884, 144), (1162, 657), (2664, 422),
  (2844, 1427), (4904, 464), (5166, 2729), (5355, 984), (5552, 2329),
  (7430, 160), (7625, 1070), (7913, 2843), (8082, 1821), (10109, 471),
  (10306, 1959), (11954, 1080), (12127, 2822), (12659, 2846), (12939, 1974)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0X0Y0_check. -/
theorem Z1Split31A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split31A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0X0Y0_pairs. -/
theorem Z1Split31A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split31A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split31A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0X0_pairs. -/
theorem Z1Split31A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split31A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split31A0_pairs. -/
theorem Z1Split31A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split31A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split31_check. -/
theorem Z1Split31_check : checkSplit m4TZ1 (1, 2, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split31A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

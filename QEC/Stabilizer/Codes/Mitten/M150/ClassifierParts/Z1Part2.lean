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
def Z1Split32A0X0Y0Certs : List (Nat × Nat) := [
  (86, 391), (98, 456), (298, 1809), (335, 2132), (995, 604),
  (1055, 939), (1073, 1055), (1198, 2097), (2636, 141), (2851, 1339),
  (2906, 1754), (2929, 1938), (4826, 203), (4834, 228), (5106, 1966),
  (5177, 2648), (5308, 417), (5523, 1847), (5561, 2178), (5622, 2778),
  (7510, 562), (7524, 619), (7593, 1028), (7774, 2585), (7861, 158),
  (8017, 976), (8066, 1318), (8215, 2603), (10037, 159), (10231, 1249),
  (10251, 1373), (10319, 1895), (11845, 469), (11977, 1309), (12091, 2232),
  (12143, 2709), (12626, 77), (12820, 1076), (12923, 1862), (12944, 2099)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0X0Y0_check. -/
theorem Z1Split32A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split32A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0X0Y0_pairs. -/
theorem Z1Split32A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split32A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split32A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0X0_pairs. -/
theorem Z1Split32A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split32A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split32A0_pairs. -/
theorem Z1Split32A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split32A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split32_check. -/
theorem Z1Split32_check : checkSplit m4TZ1 (1, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split32A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split33A0X0Y0Certs : List (Nat × Nat) := [
  (15, 528), (16, 592), (81, 1161), (82, 1307), (181, 19),
  (206, 2086), (349, 884), (350, 1003), (364, 55), (365, 68),
  (534, 1629), (535, 1840), (549, 188), (550, 221), (693, 44),
  (718, 2583), (817, 118), (818, 147), (883, 364), (884, 437)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0X0Y0_check. -/
theorem Z1Split33A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split33A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0X0Y0_pairs. -/
theorem Z1Split33A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split33A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact Z1Split33A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0X0_pairs. -/
theorem Z1Split33A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split33A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split33A0_pairs. -/
theorem Z1Split33A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split33A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split33_check. -/
theorem Z1Split33_check : checkSplit m4TZ1 (1, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split33A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split34A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0X0Y0_check. -/
theorem Z1Split34A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split34A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0X0Y0_pairs. -/
theorem Z1Split34A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split34A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact Z1Split34A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0X0_pairs. -/
theorem Z1Split34A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split34A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split34A0_pairs. -/
theorem Z1Split34A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split34A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split34_check. -/
theorem Z1Split34_check : checkSplit m4TZ1 (1, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split34A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split35A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0X0Y0_check. -/
theorem Z1Split35A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split35A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0X0Y0_pairs. -/
theorem Z1Split35A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split35A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split35A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0X0_pairs. -/
theorem Z1Split35A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split35A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split35A0_pairs. -/
theorem Z1Split35A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split35A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split35_check. -/
theorem Z1Split35_check : checkSplit m4TZ1 (2, 0, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split35A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split36A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0X0Y0_check. -/
theorem Z1Split36A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split36A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0X0Y0_pairs. -/
theorem Z1Split36A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split36A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split36A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0X0_pairs. -/
theorem Z1Split36A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split36A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split36A0_pairs. -/
theorem Z1Split36A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 3 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split36A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split36_check. -/
theorem Z1Split36_check : checkSplit m4TZ1 (2, 1, 3, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split36A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split37A0X0Y0Certs : List (Nat × Nat) := [
  (7832, 39), (26782, 1377), (31774, 112), (33594, 459), (50885, 3079),
  (64727, 2243), (72285, 352), (74154, 1059), (74553, 857), (99032, 1677)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X0Y0_check. -/
theorem Z1Split37A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X0Y0_pairs. -/
theorem Z1Split37A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split37A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X0_pairs. -/
theorem Z1Split37A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split37A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split37A0X1Y0Certs : List (Nat × Nat) := [
  (320, 1945), (574, 692), (8160, 2102), (11085, 1165), (42680, 230),
  (43903, 2794), (44630, 1485), (67555, 622), (69551, 2608), (70834, 2408)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X1Y0_check. -/
theorem Z1Split37A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X1Y0_pairs. -/
theorem Z1Split37A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split37A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M0Left_eq
    · exact Z1M0Right_eq
    · intro x hx
      exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split37A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0X1_pairs. -/
theorem Z1Split37A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split37A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37A0_pairs. -/
theorem Z1Split37A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 2 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split37A0X0_pairs x hx y hy hw
  · exact Z1Split37A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split37_check. -/
theorem Z1Split37_check : checkSplit m4TZ1 (2, 2, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split37A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split38A0X0Y0Certs : List (Nat × Nat) := [
  (54, 1626), (513, 41), (2167, 116), (4431, 1158), (4609, 887),
  (4963, 367), (8101, 14), (11224, 54), (12525, 527), (12999, 187)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0X0Y0_check. -/
theorem Z1Split38A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split38A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0X0Y0_pairs. -/
theorem Z1Split38A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split38A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
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
      exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split38A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0X0_pairs. -/
theorem Z1Split38A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split38A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split38A0_pairs. -/
theorem Z1Split38A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split38A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split38_check. -/
theorem Z1Split38_check : checkSplit m4TZ1 (2, 3, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split38A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split39A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0X0Y0_check. -/
theorem Z1Split39A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split39A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0X0Y0_pairs. -/
theorem Z1Split39A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split39A0X0Y0Certs
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
  · exact Z1Split39A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0X0_pairs. -/
theorem Z1Split39A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split39A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split39A0_pairs. -/
theorem Z1Split39A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split39A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split39_check. -/
theorem Z1Split39_check : checkSplit m4TZ1 (2, 4, 0, 0) = true := by
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
    · exact Z1Split39A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split40A0X0Y0Certs : List (Nat × Nat) := [
  (250, 351), (514, 566), (897, 848), (913, 853), (987, 903),
  (990, 906), (1206, 1052), (1455, 1251), (1475, 1260), (1581, 1337),
  (1586, 1341), (1877, 1532)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0Y0_check. -/
theorem Z1Split40A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split40A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0Y0_pairs. -/
theorem Z1Split40A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split40A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z1M2Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z1Split40A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split40A0X0Y1Certs : List (Nat × Nat) := [
  (73, 1678), (80, 1682), (198, 1758), (362, 1891), (370, 1898),
  (431, 1933), (691, 2176), (700, 2181), (840, 2274), (1032, 2424),
  (1042, 2432), (1115, 2489), (1267, 2602), (1437, 2705), (1449, 2715),
  (1667, 2973), (1878, 3103), (1893, 3113)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0Y1_check. -/
theorem Z1Split40A0X0Y1_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split40A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0Y1_pairs. -/
theorem Z1Split40A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split40A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z1M2Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z1Split40A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0X0_pairs. -/
theorem Z1Split40A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split40A0X0Y0_pairs x hx y hy hw
  · exact Z1Split40A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split40A0_pairs. -/
theorem Z1Split40A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split40A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split40_check. -/
theorem Z1Split40_check : checkSplit m4TZ1 (3, 0, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split40A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split41A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0X0Y0_check. -/
theorem Z1Split41A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split41A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0X0Y0_pairs. -/
theorem Z1Split41A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split41A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
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
      exact Z1M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact Z1Split41A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0X0_pairs. -/
theorem Z1Split41A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split41A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split41A0_pairs. -/
theorem Z1Split41A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split41A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split41_check. -/
theorem Z1Split41_check : checkSplit m4TZ1 (3, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split41A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split42A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0X0Y0_check. -/
theorem Z1Split42A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split42A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0X0Y0_pairs. -/
theorem Z1Split42A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split42A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split42A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0X0_pairs. -/
theorem Z1Split42A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split42A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split42A0_pairs. -/
theorem Z1Split42A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split42A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split42_check. -/
theorem Z1Split42_check : checkSplit m4TZ1 (3, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split42A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split43A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X0Y0_check. -/
theorem Z1Split43A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split43A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X0Y0_pairs. -/
theorem Z1Split43A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split43A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split43A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X0_pairs. -/
theorem Z1Split43A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split43A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split43A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X1Y0_check. -/
theorem Z1Split43A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split43A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X1Y0_pairs. -/
theorem Z1Split43A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split43A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split43A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0X1_pairs. -/
theorem Z1Split43A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split43A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43A0_pairs. -/
theorem Z1Split43A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split43A0X0_pairs x hx y hy hw
  · exact Z1Split43A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split43_check. -/
theorem Z1Split43_check : checkSplit m4TZ1 (3, 3, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split43A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split44A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0X0Y0_check. -/
theorem Z1Split44A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split44A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0X0Y0_pairs. -/
theorem Z1Split44A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split44A0X0Y0Certs
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
  · exact Z1Split44A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0X0_pairs. -/
theorem Z1Split44A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split44A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split44A0_pairs. -/
theorem Z1Split44A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split44A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split44_check. -/
theorem Z1Split44_check : checkSplit m4TZ1 (4, 0, 2, 2) = true := by
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
    · exact Z1Split44A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split45A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0X0Y0_check. -/
theorem Z1Split45A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split45A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0X0Y0_pairs. -/
theorem Z1Split45A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split45A0X0Y0Certs
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
  · exact Z1Split45A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0X0_pairs. -/
theorem Z1Split45A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split45A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split45A0_pairs. -/
theorem Z1Split45A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split45A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split45_check. -/
theorem Z1Split45_check : checkSplit m4TZ1 (4, 1, 1, 2) = true := by
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
    · exact Z1Split45A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split46A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0X0Y0_check. -/
theorem Z1Split46A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split46A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0X0Y0_pairs. -/
theorem Z1Split46A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split46A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split46A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0X0_pairs. -/
theorem Z1Split46A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split46A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split46A0_pairs. -/
theorem Z1Split46A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 4 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split46A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split46_check. -/
theorem Z1Split46_check : checkSplit m4TZ1 (4, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split46A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split47A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0X0Y0_check. -/
theorem Z1Split47A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split47A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0X0Y0_pairs. -/
theorem Z1Split47A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split47A0X0Y0Certs
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
  · exact Z1Split47A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0X0_pairs. -/
theorem Z1Split47A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split47A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split47A0_pairs. -/
theorem Z1Split47A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split47A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split47_check. -/
theorem Z1Split47_check : checkSplit m4TZ1 (5, 0, 1, 2) = true := by
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
    · exact Z1Split47A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

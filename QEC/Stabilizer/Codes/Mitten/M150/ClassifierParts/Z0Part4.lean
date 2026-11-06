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
def Z0Split64A0X0Y0Certs : List (Nat × Nat) := [
  (88, 354), (376, 1901), (590, 633), (705, 1216), (786, 1737),
  (1057, 798), (1304, 2312), (1755, 97), (2114, 1880), (2148, 2097),
  (2398, 961), (2673, 250), (2908, 1422), (3650, 705), (3843, 1772),
  (3976, 239), (3983, 277), (4348, 2295), (4522, 738), (5120, 1594),
  (5370, 595), (5548, 1572), (6343, 1138), (6514, 2179), (6673, 579),
  (6684, 643), (6942, 2131), (7240, 1304), (7520, 494), (7856, 128),
  (8103, 1253), (8755, 232), (9053, 1741), (9201, 272), (9282, 573),
  (9406, 1227), (9609, 181), (10246, 1055), (11013, 546), (11287, 2107),
  (11422, 447), (12086, 1628), (12257, 298), (12439, 1152), (12851, 1035)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0X0Y0_check. -/
theorem Z0Split64A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0X0Y0_pairs. -/
theorem Z0Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split64A0X0Y0Certs
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
  · exact Z0Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0X0_pairs. -/
theorem Z0Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split64A0_pairs. -/
theorem Z0Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split64_check. -/
theorem Z0Split64_check : checkSplit m4TZ0 (1, 5, 2, 0) = true := by
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
    · exact Z0Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split65A0X0Y0Certs : List (Nat × Nat) := [
  (19, 734), (84, 1291), (183, 49), (269, 2089), (367, 119),
  (431, 229), (553, 317), (617, 538), (773, 1135), (867, 1733)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0X0Y0_check. -/
theorem Z0Split65A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0X0Y0_pairs. -/
theorem Z0Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split65A0X0Y0Certs
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
  · exact Z0Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0X0_pairs. -/
theorem Z0Split65A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split65A0_pairs. -/
theorem Z0Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split65_check. -/
theorem Z0Split65_check : checkSplit m4TZ0 (1, 6, 1, 0) = true := by
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
    · exact Z0Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0X0Y0_check. -/
theorem Z0Split66A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0X0Y0_pairs. -/
theorem Z0Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split66A0X0Y0Certs
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
  · exact Z0Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0X0_pairs. -/
theorem Z0Split66A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split66A0_pairs. -/
theorem Z0Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 7 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split66_check. -/
theorem Z0Split66_check : checkSplit m4TZ0 (1, 7, 0, 0) = true := by
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
    · exact Z0Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A0X0Y0Certs : List (Nat × Nat) := [
  (71, 0), (118, 0), (326, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0X0Y0_check. -/
theorem Z0Split67A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0X0Y0_pairs. -/
theorem Z0Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A0X0Y0Certs
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
  · exact Z0Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0X0_pairs. -/
theorem Z0Split67A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A0_pairs. -/
theorem Z0Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 6 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1X0Y0_check. -/
theorem Z0Split67A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1X0Y0_pairs. -/
theorem Z0Split67A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A1X0Y0Certs
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
  · exact Z0Split67A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1X0_pairs. -/
theorem Z0Split67A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A1_pairs. -/
theorem Z0Split67A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 6 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A2X0Y0Certs : List (Nat × Nat) := [
  (229, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2X0Y0_check. -/
theorem Z0Split67A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2X0Y0_pairs. -/
theorem Z0Split67A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A2X0Y0Certs
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
  · exact Z0Split67A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2X0_pairs. -/
theorem Z0Split67A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A2_pairs. -/
theorem Z0Split67A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 6 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split67A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3X0Y0_check. -/
theorem Z0Split67A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3X0Y0_pairs. -/
theorem Z0Split67A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split67A3X0Y0Certs
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
  · exact Z0Split67A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3X0_pairs. -/
theorem Z0Split67A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split67A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67A3_pairs. -/
theorem Z0Split67A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 6 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split67A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split67_check. -/
theorem Z0Split67_check : checkSplit m4TZ0 (2, 0, 6, 3) = true := by
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
    · exact Z0Split67A0_pairs x hx y hy hw
    · exact Z0Split67A1_pairs x hx y hy hw
    · exact Z0Split67A2_pairs x hx y hy hw
    · exact Z0Split67A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A0X0Y0Certs : List (Nat × Nat) := [
  (83, 0), (563, 677), (1107, 0), (1154, 0), (1241, 1329),
  (1468, 0), (1743, 1713), (2003, 0), (2217, 819), (3083, 0),
  (3467, 457), (3734, 1693), (4183, 1855), (4297, 1540), (4552, 0),
  (4739, 0), (4778, 0), (5009, 1348), (5141, 689), (5360, 0),
  (5537, 0), (5705, 0), (6270, 0), (6368, 0), (6478, 1497),
  (6803, 985), (6987, 1129), (7220, 1711), (7911, 0), (8357, 955),
  (8603, 0), (9899, 1652), (9923, 0), (10225, 858), (10868, 0),
  (10944, 899), (11004, 0), (11179, 0), (11538, 1541), (11649, 0),
  (11793, 0), (12066, 0), (12753, 1557), (12852, 0), (12924, 1109)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0X0Y0_check. -/
theorem Z0Split68A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0X0Y0_pairs. -/
theorem Z0Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A0X0Y0Certs
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
  · exact Z0Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0X0_pairs. -/
theorem Z0Split68A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A0_pairs. -/
theorem Z0Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A1X0Y0Certs : List (Nat × Nat) := [
  (809, 0), (1388, 2030), (1930, 0), (2220, 2084), (5706, 2076),
  (7993, 2086), (8617, 2067), (11806, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1X0Y0_check. -/
theorem Z0Split68A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1X0Y0_pairs. -/
theorem Z0Split68A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A1X0Y0Certs
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
  · exact Z0Split68A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1X0_pairs. -/
theorem Z0Split68A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A1_pairs. -/
theorem Z0Split68A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A2X0Y0Certs : List (Nat × Nat) := [
  (2108, 0), (5012, 2276), (6092, 0), (6652, 0), (7097, 0),
  (7819, 2159), (8164, 0), (9072, 2205), (10622, 0), (10717, 0),
  (11119, 2169), (11634, 0), (11957, 0), (12617, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2X0Y0_check. -/
theorem Z0Split68A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2X0Y0_pairs. -/
theorem Z0Split68A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A2X0Y0Certs
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
  · exact Z0Split68A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2X0_pairs. -/
theorem Z0Split68A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A2_pairs. -/
theorem Z0Split68A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split68A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3X0Y0_check. -/
theorem Z0Split68A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3X0Y0_pairs. -/
theorem Z0Split68A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split68A3X0Y0Certs
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
  · exact Z0Split68A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3X0_pairs. -/
theorem Z0Split68A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split68A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68A3_pairs. -/
theorem Z0Split68A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split68A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split68_check. -/
theorem Z0Split68_check : checkSplit m4TZ0 (2, 1, 5, 3) = true := by
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
    · exact Z0Split68A0_pairs x hx y hy hw
    · exact Z0Split68A1_pairs x hx y hy hw
    · exact Z0Split68A2_pairs x hx y hy hw
    · exact Z0Split68A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A0X0Y0Certs : List (Nat × Nat) := [
  (110, 0), (1059, 0), (1301, 563), (4042, 0), (6519, 0),
  (6816, 0), (6928, 850), (7935, 0), (8019, 361), (8034, 0),
  (8061, 1872), (8654, 1188), (10448, 1518), (10799, 1910), (11087, 0),
  (11741, 1516), (12209, 0), (13363, 587), (14213, 716), (14500, 1417),
  (14983, 1722), (16855, 0), (17012, 1273), (19980, 0), (20695, 0),
  (22339, 0), (23538, 0), (24279, 679), (24347, 1785), (24759, 0),
  (25720, 0), (28423, 258), (28620, 0), (28662, 1655), (28914, 1106),
  (29966, 1476), (30306, 1411), (30935, 0), (32031, 811), (32769, 1841),
  (34697, 0), (37665, 953), (38846, 0), (39987, 1384), (41296, 991),
  (42592, 1243), (43642, 0), (43756, 1224), (44203, 666), (44475, 411),
  (44533, 0), (44559, 0), (45904, 0), (47586, 0), (47693, 0),
  (48296, 0), (48846, 1886), (49121, 0), (50010, 1281), (50142, 0),
  (50611, 0), (51820, 0), (53271, 0), (54097, 0), (54213, 0),
  (54382, 1612), (55740, 0), (55948, 453), (57044, 1596), (57288, 0),
  (57354, 1176), (58072, 0), (59917, 1407), (60443, 852), (60837, 1791),
  (62711, 0), (63131, 0), (65785, 0), (66233, 1372), (66391, 613),
  (67156, 0), (67745, 1681), (68777, 1887), (69813, 1521), (70354, 781),
  (72215, 1440), (72230, 942), (73826, 0), (74412, 1827), (74461, 588),
  (75337, 348), (75863, 0), (77150, 0), (78734, 0), (80157, 1044),
  (80283, 0), (80832, 672), (81489, 1053), (82842, 0), (83551, 1252),
  (85659, 0), (85752, 1171), (87663, 1238), (88154, 1839), (88361, 402),
  (89533, 1891), (89982, 646), (90257, 900), (90871, 1236), (93263, 0),
  (96341, 791), (96547, 0), (98076, 1924), (98886, 957), (99017, 1001),
  (103438, 1099), (104747, 0), (104875, 857), (104913, 0), (105461, 1597),
  (106667, 1073), (106947, 978), (107160, 0), (108025, 502), (108286, 1814)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X0Y0_check. -/
theorem Z0Split69A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X0Y0_pairs. -/
theorem Z0Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X0_pairs. -/
theorem Z0Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A0X1Y0Certs : List (Nat × Nat) := [
  (698, 718), (810, 1218), (2144, 1494), (2562, 1126), (2699, 1485),
  (2952, 1489), (6301, 358), (7392, 0), (9614, 570), (9794, 1060),
  (9921, 1284), (11044, 1245), (11310, 873), (11711, 1261), (11755, 1641),
  (12795, 794), (13854, 1625), (14850, 0), (15058, 1697), (16800, 0),
  (18498, 1614), (18587, 599), (19123, 755), (19208, 0), (19842, 1626),
  (20624, 1807), (21464, 885), (21723, 0), (21725, 0), (21914, 1347),
  (22679, 1004), (22929, 1420), (23153, 1900), (23871, 0), (24242, 868),
  (24415, 0), (25227, 0), (26242, 1806), (26955, 1043), (27112, 0),
  (27840, 1816), (28702, 0), (28850, 886), (30422, 349), (30466, 1558),
  (31328, 0), (31370, 0), (31755, 0), (32093, 0), (32996, 1013),
  (35881, 1104), (36550, 1706), (38124, 0), (38394, 1495), (39019, 533),
  (39656, 0), (40214, 1662), (40427, 979), (41236, 0), (41593, 1074),
  (42494, 0), (43184, 0), (43255, 0), (44737, 1231), (44779, 1882),
  (44947, 1859), (45177, 1664), (45470, 0), (45544, 0), (46152, 1896),
  (47093, 1663), (48344, 806), (49721, 0), (50866, 0), (51337, 808),
  (51351, 0), (52172, 0), (54059, 1211), (54131, 1636), (54348, 1923),
  (54432, 0), (57257, 1539), (57556, 688), (58870, 1327), (59118, 1474),
  (59229, 0), (59268, 0), (59274, 1724), (60866, 1509), (62835, 0),
  (63007, 0), (63049, 0), (63165, 0), (63276, 1613), (65077, 1542),
  (65744, 796), (68960, 1875), (69034, 1125), (70197, 161), (70891, 0),
  (70898, 1765), (71312, 1425), (72735, 0), (73181, 675), (73270, 0),
  (73739, 1426), (74684, 1388), (74746, 1439), (74965, 1432), (75745, 0),
  (76557, 0), (77470, 1434), (77756, 0), (79017, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X1Y0_check. -/
theorem Z0Split69A0X1Y0_check : checkGrid m4TZ0 censusZ0 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X1Y0_pairs. -/
theorem Z0Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0X1_pairs. -/
theorem Z0Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A0_pairs. -/
theorem Z0Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A0X0_pairs x hx y hy hw
  · exact Z0Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A1X0Y0Certs : List (Nat × Nat) := [
  (13851, 2087), (17759, 2009), (28535, 0), (32565, 2085), (33952, 1953),
  (37017, 2047), (37445, 0), (38669, 2048), (38773, 0), (45112, 2004),
  (52411, 0), (55898, 1994), (61296, 0), (62865, 2042), (66502, 2059),
  (69264, 1996), (72644, 0), (82712, 1982), (86489, 2011), (91721, 2065),
  (93928, 0), (94829, 0), (102885, 2025)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X0Y0_check. -/
theorem Z0Split69A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X0Y0_pairs. -/
theorem Z0Split69A1X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X0_pairs. -/
theorem Z0Split69A1X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A1X1Y0Certs : List (Nat × Nat) := [
  (577, 0), (3723, 0), (19557, 0), (43452, 0), (46578, 2024),
  (48038, 2015), (48108, 2019), (54572, 2060), (54793, 0), (58877, 0),
  (66190, 2056)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X1Y0_check. -/
theorem Z0Split69A1X1Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X1Y0_pairs. -/
theorem Z0Split69A1X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A1X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1X1_pairs. -/
theorem Z0Split69A1X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A1_pairs. -/
theorem Z0Split69A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A1X0_pairs x hx y hy hw
  · exact Z0Split69A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A2X0Y0Certs : List (Nat × Nat) := [
  (3446, 2268), (6854, 0), (11234, 0), (19701, 2309), (28576, 2293),
  (31991, 0), (32082, 2289), (43057, 2213), (50609, 2165), (50796, 2162),
  (53313, 2290), (57519, 0), (60272, 2204), (67061, 0), (69992, 0),
  (73054, 2264), (73347, 2275), (74826, 0), (75163, 2228), (79376, 0),
  (80241, 2288), (91181, 0), (92102, 2308), (97248, 2307), (98118, 0),
  (105620, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X0Y0_check. -/
theorem Z0Split69A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X0Y0_pairs. -/
theorem Z0Split69A2X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X0_pairs. -/
theorem Z0Split69A2X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A2X1Y0Certs : List (Nat × Nat) := [
  (3452, 2218), (5619, 0), (10965, 2212), (25314, 0), (28369, 2273),
  (29999, 2300), (39751, 0), (41382, 2246), (45803, 0), (54992, 2147),
  (55535, 2237), (59798, 2153), (62905, 2236), (64388, 2250), (67522, 0),
  (68791, 2254), (70532, 2301), (71170, 2190), (72762, 2177), (72803, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X1Y0_check. -/
theorem Z0Split69A2X1Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X1Y0_pairs. -/
theorem Z0Split69A2X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A2X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2X1_pairs. -/
theorem Z0Split69A2X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A2_pairs. -/
theorem Z0Split69A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A2X0_pairs x hx y hy hw
  · exact Z0Split69A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A3X0Y0Certs : List (Nat × Nat) := [
  (37395, 2323)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X0Y0_check. -/
theorem Z0Split69A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X0Y0_pairs. -/
theorem Z0Split69A3X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X0_pairs. -/
theorem Z0Split69A3X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split69A3X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X1Y0_check. -/
theorem Z0Split69A3X1Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X1Y0_pairs. -/
theorem Z0Split69A3X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split69A3X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M3Left_eq
    · exact Z0M3Right_eq
    · intro x hx
      exact Z0M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split69A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3X1_pairs. -/
theorem Z0Split69A3X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split69A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69A3_pairs. -/
theorem Z0Split69A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split69A3X0_pairs x hx y hy hw
  · exact Z0Split69A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split69_check. -/
theorem Z0Split69_check : checkSplit m4TZ0 (2, 2, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split69A0_pairs x hx y hy hw
    · exact Z0Split69A1_pairs x hx y hy hw
    · exact Z0Split69A2_pairs x hx y hy hw
    · exact Z0Split69A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y0Certs : List (Nat × Nat) := [
  (4935, 391), (8611, 400), (14740, 241), (28853, 248), (36060, 193),
  (43502, 302), (46124, 235), (46749, 357), (63277, 108), (97959, 215),
  (102195, 301)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y0_check. -/
theorem Z0Split70A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y0_pairs. -/
theorem Z0Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y1Certs : List (Nat × Nat) := [
  (16765, 514), (16864, 562), (20174, 596), (20730, 512), (26455, 474),
  (34834, 520), (36393, 583), (46348, 507), (51583, 597), (52322, 605),
  (54459, 593), (63273, 473), (72119, 575), (74616, 559), (80614, 492),
  (89227, 462)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y1_check. -/
theorem Z0Split70A0X0Y1_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y1_pairs. -/
theorem Z0Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y2Certs : List (Nat × Nat) := [
  (21660, 802), (22211, 760), (36334, 655), (51317, 701), (62022, 709),
  (64618, 710), (67355, 807)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y2_check. -/
theorem Z0Split70A0X0Y2_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y2_pairs. -/
theorem Z0Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y2Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y3Certs : List (Nat × Nat) := [
  (15861, 951), (18880, 871), (29342, 882), (66731, 990), (66797, 1014),
  (81452, 943), (84944, 884)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y3_check. -/
theorem Z0Split70A0X0Y3_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y3_pairs. -/
theorem Z0Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y3Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y4Certs : List (Nat × Nat) := [
  (14335, 1179), (21825, 1056), (37618, 1203), (60151, 1093), (60348, 1187),
  (67220, 1257), (68855, 1088), (83041, 1168), (83286, 1050), (96218, 1230),
  (96966, 1105), (97588, 1181), (99610, 1233), (114728, 1038), (117182, 1059),
  (118684, 1082)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y4_check. -/
theorem Z0Split70A0X0Y4_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y4_pairs. -/
theorem Z0Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y4Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y5Certs : List (Nat × Nat) := [
  (25847, 1397), (43018, 1427), (43972, 1355), (54190, 1358), (67761, 1378)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y5_check. -/
theorem Z0Split70A0X0Y5_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y5_pairs. -/
theorem Z0Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y5Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y6Certs : List (Nat × Nat) := [
  (1342, 1502), (5067, 1538), (7369, 1510), (32572, 1512), (37977, 1513),
  (50065, 1536), (51554, 1533), (68358, 1535)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y6_check. -/
theorem Z0Split70A0X0Y6_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y6_pairs. -/
theorem Z0Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y6Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y7Certs : List (Nat × Nat) := [
  (4956, 1607), (18588, 1601), (21058, 1696), (23841, 1624), (37907, 1675),
  (39772, 1629), (41782, 1656), (59830, 1589), (78252, 1694)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y7_check. -/
theorem Z0Split70A0X0Y7_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y7_pairs. -/
theorem Z0Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y7Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y8Certs : List (Nat × Nat) := [
  (11166, 1895), (17785, 1871), (30403, 1854), (30698, 1823), (33209, 1852),
  (33504, 1821), (49129, 1920), (53051, 1767), (58925, 1905), (59900, 1865),
  (84446, 1838)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y8_check. -/
theorem Z0Split70A0X0Y8_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y8_pairs. -/
theorem Z0Split70A0X0Y8_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y8Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk8
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk8_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z0Split70A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y9Certs : List (Nat × Nat) := [
  (9715, 2036), (10768, 2016), (26831, 2082), (28245, 2038), (32361, 2026),
  (39792, 1981), (54781, 2068), (65007, 2079), (74996, 2007), (81606, 2058),
  (82306, 2041), (92142, 2044)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y9_check. -/
theorem Z0Split70A0X0Y9_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y9_pairs. -/
theorem Z0Split70A0X0Y9_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y9Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk9
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk9_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z0Split70A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X0Y10Certs : List (Nat × Nat) := [
  (7352, 2126), (7548, 2226), (11789, 2109), (12137, 2304), (13695, 2257),
  (38734, 2185), (39896, 2161), (46037, 2183), (47462, 2306), (53114, 2287),
  (66080, 2263), (75189, 2152), (75607, 2158), (77532, 2317), (80028, 2128),
  (80860, 2141), (92383, 2216)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y10_check. -/
theorem Z0Split70A0X0Y10_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0Y10_pairs. -/
theorem Z0Split70A0X0Y10_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X0Y10Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk0 masks3S512Chunk10
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk10_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z0Split70A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X0_pairs. -/
theorem Z0Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z0Split70A0X0Y0_pairs x hx y hy hw
  · exact Z0Split70A0X0Y1_pairs x hx y hy hw
  · exact Z0Split70A0X0Y2_pairs x hx y hy hw
  · exact Z0Split70A0X0Y3_pairs x hx y hy hw
  · exact Z0Split70A0X0Y4_pairs x hx y hy hw
  · exact Z0Split70A0X0Y5_pairs x hx y hy hw
  · exact Z0Split70A0X0Y6_pairs x hx y hy hw
  · exact Z0Split70A0X0Y7_pairs x hx y hy hw
  · exact Z0Split70A0X0Y8_pairs x hx y hy hw
  · exact Z0Split70A0X0Y9_pairs x hx y hy hw
  · exact Z0Split70A0X0Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y0Certs : List (Nat × Nat) := [
  (3456, 297), (6439, 154), (19494, 389), (36538, 217), (50716, 257),
  (54106, 397)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y0_check. -/
theorem Z0Split70A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y0_pairs. -/
theorem Z0Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y1Certs : List (Nat × Nat) := [
  (642, 576), (21824, 516), (24130, 591), (50470, 581), (52946, 556),
  (57668, 568), (60530, 557), (61128, 495), (62441, 610)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y1_check. -/
theorem Z0Split70A0X1Y1_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y1_pairs. -/
theorem Z0Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y2Certs : List (Nat × Nat) := [
  (14144, 780), (17881, 663), (20145, 662), (29191, 649), (36096, 704),
  (37496, 787)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y2_check. -/
theorem Z0Split70A0X1Y2_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y2_pairs. -/
theorem Z0Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y2Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y3Certs : List (Nat × Nat) := [
  (10476, 869), (13193, 1012), (17657, 863), (19663, 864), (23624, 853),
  (37936, 995), (71333, 879)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y3_check. -/
theorem Z0Split70A0X1Y3_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y3_pairs. -/
theorem Z0Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y3Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y4Certs : List (Nat × Nat) := [
  (2635, 1122), (6239, 1258), (7231, 1272), (10094, 1251), (16927, 1279),
  (24930, 1153), (29994, 1277), (30305, 1178), (30377, 1219), (33714, 1184),
  (37620, 1209), (44807, 1169), (48047, 1090), (49739, 1221), (64227, 1197),
  (69841, 1096), (72522, 1249), (78510, 1081), (82304, 1039), (83401, 1102)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y4_check. -/
theorem Z0Split70A0X1Y4_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y4_pairs. -/
theorem Z0Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y4Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y5Certs : List (Nat × Nat) := [
  (13945, 1380), (19571, 1433), (29313, 1339), (30207, 1370), (40584, 1309),
  (42278, 1333), (47259, 1341), (48757, 1398)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y5_check. -/
theorem Z0Split70A0X1Y5_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y5_pairs. -/
theorem Z0Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y5Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y6Certs : List (Nat × Nat) := [
  (15881, 1550), (39450, 1503), (41050, 1530), (41765, 1482), (42985, 1486)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y6_check. -/
theorem Z0Split70A0X1Y6_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y6_pairs. -/
theorem Z0Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y6Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y7Certs : List (Nat × Nat) := [
  (3660, 1608), (4144, 1687), (8886, 1620), (10343, 1702), (11051, 1571),
  (20646, 1650), (27376, 1606), (28286, 1579), (29060, 1635), (30109, 1676),
  (35146, 1595), (37876, 1653), (49703, 1720), (51273, 1689)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y7_check. -/
theorem Z0Split70A0X1Y7_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y7_pairs. -/
theorem Z0Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y7Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y8Certs : List (Nat × Nat) := [
  (2419, 1906), (8899, 1798), (18379, 1800), (21426, 1755), (22630, 1825),
  (23934, 1774), (41032, 1907), (41609, 1836), (43467, 1898), (47102, 1775),
  (51234, 1918), (51401, 1818), (51505, 1883), (53187, 1832), (57124, 1885)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y8_check. -/
theorem Z0Split70A0X1Y8_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y8_pairs. -/
theorem Z0Split70A0X1Y8_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y8Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk8
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk8_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z0Split70A0X1Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y9Certs : List (Nat × Nat) := [
  (739, 2075), (9805, 2072), (37859, 1969), (51078, 1964), (51472, 1971),
  (60884, 1954)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y9_check. -/
theorem Z0Split70A0X1Y9_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y9_pairs. -/
theorem Z0Split70A0X1Y9_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y9Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk9
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk9_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z0Split70A0X1Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split70A0X1Y10Certs : List (Nat × Nat) := [
  (301, 2260), (3057, 2210), (8656, 2167), (10178, 2121), (22525, 2203),
  (35644, 2272), (41540, 2166), (45057, 2318), (51311, 2180), (55054, 2229),
  (58938, 2142), (60259, 2194), (62518, 2319), (72572, 2262), (73489, 2101)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y10_check. -/
theorem Z0Split70A0X1Y10_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1Y10_pairs. -/
theorem Z0Split70A0X1Y10_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z0M0LeftColumns Z0M0RightColumns) Z0Split70A0X1Y10Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks2S256Chunk1 masks3S512Chunk10
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk10_bound
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
      exact Z0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z0Split70A0X1Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0X1_pairs. -/
theorem Z0Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z0Split70A0X1Y0_pairs x hx y hy hw
  · exact Z0Split70A0X1Y1_pairs x hx y hy hw
  · exact Z0Split70A0X1Y2_pairs x hx y hy hw
  · exact Z0Split70A0X1Y3_pairs x hx y hy hw
  · exact Z0Split70A0X1Y4_pairs x hx y hy hw
  · exact Z0Split70A0X1Y5_pairs x hx y hy hw
  · exact Z0Split70A0X1Y6_pairs x hx y hy hw
  · exact Z0Split70A0X1Y7_pairs x hx y hy hw
  · exact Z0Split70A0X1Y8_pairs x hx y hy hw
  · exact Z0Split70A0X1Y9_pairs x hx y hy hw
  · exact Z0Split70A0X1Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70A0_pairs. -/
theorem Z0Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split70A0X0_pairs x hx y hy hw
  · exact Z0Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split70_check. -/
theorem Z0Split70_check : checkSplit m4TZ0 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split71A0X0Y0Certs : List (Nat × Nat) := [
  (3462, 2133), (5809, 630), (6699, 744), (8250, 2156), (11738, 2224),
  (12584, 2055), (12972, 1754), (13032, 2132), (13997, 299), (14056, 542),
  (16448, 1740), (17547, 574), (20190, 764), (21904, 629), (22089, 1611),
  (22626, 64), (24969, 745), (27786, 1943), (27818, 2116), (28100, 1156),
  (28888, 756), (29863, 1316), (31956, 860), (33508, 81), (34582, 928),
  (36510, 2071), (38616, 1598), (40156, 544), (40488, 153), (41472, 572),
  (41743, 2140), (41829, 278), (43213, 580), (43670, 707), (43755, 1145),
  (46280, 706), (47265, 1322), (47827, 2106), (49172, 101), (49860, 1214),
  (50565, 424), (50611, 602), (54231, 1361), (54789, 2120), (54803, 2223),
  (55711, 151), (55789, 435), (56556, 65), (56745, 847), (57176, 838),
  (57893, 176), (60821, 1749), (61706, 1833), (62053, 1315), (62867, 987),
  (65285, 158), (65339, 359), (66049, 1779), (67714, 1350), (69246, 328),
  (72527, 1501), (74002, 218), (74786, 2034), (76204, 324), (78105, 1048),
  (79149, 2119), (81486, 552), (83250, 664), (84170, 925), (84645, 1143),
  (85361, 396), (86283, 627), (86729, 660), (86835, 1215), (87160, 645),
  (87578, 558), (87703, 1193), (89011, 1226), (89428, 1139), (89532, 1752),
  (92218, 2296), (93343, 1137), (93607, 331), (94503, 431), (94994, 661),
  (95342, 300), (97512, 284), (98249, 1878), (98957, 916), (99019, 1264),
  (101997, 881), (102923, 1166), (102983, 1532), (104613, 919), (104937, 398),
  (105171, 1599), (106673, 390), (106794, 933), (107483, 177), (107755, 1470),
  (108184, 1457), (108861, 439)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X0Y0_check. -/
theorem Z0Split71A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X0Y0_pairs. -/
theorem Z0Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X0Y0Certs
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
  · exact Z0Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X0_pairs. -/
theorem Z0Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split71A0X1Y0Certs : List (Nat × Nat) := [
  (133, 521), (451, 99), (787, 1738), (3461, 2127), (3868, 1960),
  (4781, 2259), (4833, 209), (4868, 337), (4963, 757), (5132, 1684),
  (5301, 327), (6344, 1141), (8804, 405), (8888, 809), (9560, 2191),
  (11234, 1763), (14095, 748), (15138, 1695), (16435, 1618), (17067, 399),
  (19838, 1165), (22338, 626), (22834, 922), (22939, 1511), (23536, 205),
  (23997, 283), (24717, 1753), (25575, 1667), (25871, 878), (26536, 35),
  (27106, 543), (27344, 1879), (27483, 323), (28106, 1183), (28212, 1847),
  (29496, 1736), (29933, 1739), (29998, 2138), (32992, 1796), (33717, 946),
  (33734, 1041), (34688, 1531), (35082, 1310), (36037, 1797), (36075, 2070),
  (36372, 1186), (37867, 121), (38421, 553), (38487, 880), (40126, 426),
  (40223, 870), (41001, 440), (41284, 1989), (41712, 1958), (41982, 945),
  (43352, 1337), (43750, 1107), (44440, 280), (44780, 2102), (44918, 450),
  (46169, 236), (46540, 2252), (47545, 511), (47649, 1028), (47698, 1314),
  (47759, 1649), (48416, 515), (48848, 504), (49979, 1967), (50152, 499),
  (50206, 772), (50314, 1351), (50355, 1578), (50638, 758), (51685, 1747),
  (53714, 892), (53804, 1436), (54974, 659), (55222, 2108), (57916, 240),
  (58291, 36), (58762, 175), (59127, 2039), (59276, 458), (60154, 490),
  (60630, 665), (61318, 2139), (62075, 1459), (62527, 1528), (63092, 100),
  (63765, 1142), (63943, 2294), (64118, 741), (64750, 1829), (64787, 2095),
  (65658, 2096), (66844, 1352), (68434, 549), (69514, 1709), (70534, 251),
  (70632, 652), (71129, 970), (72703, 234), (72790, 566), (74031, 326),
  (74197, 1087), (74231, 1307), (74282, 1587), (75068, 1094), (75500, 1076),
  (76269, 560), (76610, 213), (76734, 743), (76804, 1067), (76852, 1369),
  (77845, 2122), (79059, 1544), (79089, 1744)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X1Y0_check. -/
theorem Z0Split71A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X1Y0_pairs. -/
theorem Z0Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split71A0X1Y0Certs
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
  · exact Z0Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0X1_pairs. -/
theorem Z0Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71A0_pairs. -/
theorem Z0Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split71A0X0_pairs x hx y hy hw
  · exact Z0Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split71_check. -/
theorem Z0Split71_check : checkSplit m4TZ0 (2, 4, 2, 0) = true := by
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
    · exact Z0Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split72A0X0Y0Certs : List (Nat × Nat) := [
  (150, 4), (212, 34), (318, 621), (812, 33), (872, 29),
  (1206, 94), (1351, 18), (1410, 11), (2706, 87), (2778, 625),
  (2856, 93), (2972, 30), (3417, 1734), (3432, 262), (3664, 61),
  (3782, 32), (4761, 908), (5682, 266), (5741, 227), (5820, 7),
  (5982, 269), (6126, 91), (6330, 10), (6552, 270), (6749, 2093),
  (6768, 619), (7119, 170), (7296, 85), (7923, 46), (8298, 622),
  (9137, 539), (9272, 27), (9468, 624), (9612, 261), (10125, 416),
  (10302, 264), (10879, 733), (11047, 112), (11580, 9), (11633, 1136),
  (11796, 90), (11970, 5), (12108, 618), (12714, 1289), (12883, 316)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0X0Y0_check. -/
theorem Z0Split72A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0X0Y0_pairs. -/
theorem Z0Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split72A0X0Y0Certs
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
  · exact Z0Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0X0_pairs. -/
theorem Z0Split72A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split72A0_pairs. -/
theorem Z0Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split72_check. -/
theorem Z0Split72_check : checkSplit m4TZ0 (2, 5, 1, 0) = true := by
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
    · exact Z0Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0X0Y0_check. -/
theorem Z0Split73A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0X0Y0_pairs. -/
theorem Z0Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split73A0X0Y0Certs
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
  · exact Z0Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0X0_pairs. -/
theorem Z0Split73A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split73A0_pairs. -/
theorem Z0Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 6 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z0Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split73_check. -/
theorem Z0Split73_check : checkSplit m4TZ0 (2, 6, 0, 0) = true := by
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
    · exact Z0Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A0X0Y0Certs : List (Nat × Nat) := [
  (175, 1682), (388, 0), (413, 670), (435, 1009), (727, 1401),
  (1013, 600), (1026, 1728), (1269, 723), (1303, 1415), (1523, 1911),
  (1778, 0), (1840, 859), (1897, 1429)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X0Y0_check. -/
theorem Z0Split74A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X0Y0_pairs. -/
theorem Z0Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X0_pairs. -/
theorem Z0Split74A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A0X1Y0Certs : List (Nat × Nat) := [
  (119, 1262), (396, 334), (522, 1267), (610, 1364), (1061, 1498),
  (1144, 1633), (1485, 767), (1598, 1790), (1623, 0), (1927, 1874),
  (1973, 1085)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X1Y0_check. -/
theorem Z0Split74A0X1Y0_check : checkGrid m4TZ0 censusZ0 3 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X1Y0_pairs. -/
theorem Z0Split74A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0X1_pairs. -/
theorem Z0Split74A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A0_pairs. -/
theorem Z0Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 5 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split74A0X0_pairs x hx y hy hw
  · exact Z0Split74A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A1X0Y0Certs : List (Nat × Nat) := [
  (705, 2054), (1858, 2078)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X0Y0_check. -/
theorem Z0Split74A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X0Y0_pairs. -/
theorem Z0Split74A1X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X0_pairs. -/
theorem Z0Split74A1X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A1X1Y0Certs : List (Nat × Nat) := [
  (142, 2061), (1708, 2031)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X1Y0_check. -/
theorem Z0Split74A1X1Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X1Y0_pairs. -/
theorem Z0Split74A1X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A1X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1X1_pairs. -/
theorem Z0Split74A1X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A1_pairs. -/
theorem Z0Split74A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 5 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split74A1X0_pairs x hx y hy hw
  · exact Z0Split74A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A2X0Y0Certs : List (Nat × Nat) := [
  (67, 2217), (169, 2292)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X0Y0_check. -/
theorem Z0Split74A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X0Y0_pairs. -/
theorem Z0Split74A2X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X0_pairs. -/
theorem Z0Split74A2X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A2X1Y0Certs : List (Nat × Nat) := [
  (1087, 2247), (1334, 2186), (1519, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X1Y0_check. -/
theorem Z0Split74A2X1Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X1Y0_pairs. -/
theorem Z0Split74A2X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A2X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2X1_pairs. -/
theorem Z0Split74A2X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A2_pairs. -/
theorem Z0Split74A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 5 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split74A2X0_pairs x hx y hy hw
  · exact Z0Split74A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X0Y0_check. -/
theorem Z0Split74A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X0Y0_pairs. -/
theorem Z0Split74A3X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X0_pairs. -/
theorem Z0Split74A3X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split74A3X1Y0Certs : List (Nat × Nat) := [
  (298, 2321), (1162, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X1Y0_check. -/
theorem Z0Split74A3X1Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X1Y0_pairs. -/
theorem Z0Split74A3X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split74A3X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z0Split74A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3X1_pairs. -/
theorem Z0Split74A3X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split74A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74A3_pairs. -/
theorem Z0Split74A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 5 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split74A3X0_pairs x hx y hy hw
  · exact Z0Split74A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split74_check. -/
theorem Z0Split74_check : checkSplit m4TZ0 (3, 0, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split74A0_pairs x hx y hy hw
    · exact Z0Split74A1_pairs x hx y hy hw
    · exact Z0Split74A2_pairs x hx y hy hw
    · exact Z0Split74A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A0X0Y0Certs : List (Nat × Nat) := [
  (3445, 954), (3600, 1282), (3915, 0), (4320, 1477), (4425, 0),
  (4734, 0), (6443, 0), (6649, 974), (7053, 1514), (7460, 1657),
  (9548, 0), (14208, 1189), (15093, 1386), (15418, 0), (16588, 676),
  (17042, 1921), (17442, 0), (17932, 0), (18518, 0), (19089, 0),
  (19138, 0), (19224, 1677), (19568, 0), (20313, 0), (22237, 1205),
  (22980, 1813), (24525, 0), (24883, 1802), (24943, 695), (25014, 872),
  (25608, 0), (26563, 0), (27026, 0), (27269, 1330), (27295, 1381),
  (27463, 1349), (27751, 0), (30186, 1098), (31847, 0), (32434, 0),
  (34391, 472), (34678, 1200), (35239, 1359), (35597, 0), (36529, 1616),
  (36949, 699), (40243, 0), (40919, 0), (41088, 1858), (42090, 1842),
  (42362, 517), (43717, 105), (44658, 611), (45968, 803), (46539, 0),
  (46622, 0), (47820, 0), (48583, 294), (48809, 191), (49413, 0),
  (51513, 1554), (51726, 1124), (54777, 0), (54815, 722), (56681, 0),
  (57583, 1867), (59281, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X0Y0_check. -/
theorem Z0Split75A0X0Y0_check : checkGrid m4TZ0 censusZ0 3 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X0Y0_pairs. -/
theorem Z0Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X0_pairs. -/
theorem Z0Split75A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A0X1Y0Certs : List (Nat × Nat) := [
  (408, 851), (1254, 1005), (1485, 0), (2194, 0), (3282, 1705),
  (5867, 1006), (5943, 0), (8648, 0), (9437, 1011), (9743, 1387),
  (9954, 1671), (10125, 0), (10328, 1862), (10515, 0), (10628, 0),
  (11190, 0), (11394, 889), (12528, 1815), (12914, 1428), (13404, 898),
  (14064, 1010), (14231, 412), (16634, 0), (18630, 0), (18744, 0),
  (18953, 0), (20802, 1602), (22549, 698), (22841, 469), (23322, 1177),
  (26142, 1647), (27338, 0), (29923, 0), (30133, 1632), (30872, 1793),
  (31240, 1265), (33818, 0), (34241, 0), (35074, 0), (35916, 1831),
  (36585, 0), (37148, 0), (37760, 1621), (38215, 0), (38321, 0),
  (39438, 1237), (40268, 0), (40363, 763), (40519, 0), (40913, 1488),
  (41397, 638), (41703, 1517), (43523, 1559), (43803, 1524), (45153, 1555),
  (46743, 1484), (46997, 901), (50613, 1639), (51101, 0), (51506, 0),
  (51823, 1046), (52382, 0), (53302, 0), (55159, 1078), (55736, 958),
  (56776, 1766)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X1Y0_check. -/
theorem Z0Split75A0X1Y0_check : checkGrid m4TZ0 censusZ0 3 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X1Y0_pairs. -/
theorem Z0Split75A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0X1_pairs. -/
theorem Z0Split75A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A0_pairs. -/
theorem Z0Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 0) = 4 →
      sweepAccept m4TZ0 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split75A0X0_pairs x hx y hy hw
  · exact Z0Split75A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A1X0Y0Certs : List (Nat × Nat) := [
  (19352, 1998), (20326, 0), (26527, 2045), (29256, 2080), (42147, 2018),
  (54157, 2049)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X0Y0_check. -/
theorem Z0Split75A1X0Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X0Y0_pairs. -/
theorem Z0Split75A1X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A1X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X0_pairs. -/
theorem Z0Split75A1X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A1X1Y0Certs : List (Nat × Nat) := [
  (702, 0), (2017, 0), (2231, 0), (9127, 1979), (11277, 2077),
  (25927, 2035), (27937, 2062), (39787, 2013), (59454, 2027)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X1Y0_check. -/
theorem Z0Split75A1X1Y0_check : checkGrid m4TZ0 censusZ0 3 376821623 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A1X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X1Y0_pairs. -/
theorem Z0Split75A1X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 376821623 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A1X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A1X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1X1_pairs. -/
theorem Z0Split75A1X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A1X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A1_pairs. -/
theorem Z0Split75A1_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 376821623) = 4 →
      sweepAccept m4TZ0 3 x y 376821623 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split75A1X0_pairs x hx y hy hw
  · exact Z0Split75A1X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A2X0Y0Certs : List (Nat × Nat) := [
  (1102, 0), (4249, 2232), (6358, 0), (14310, 2184), (24352, 0),
  (26852, 2277), (31532, 0), (39698, 0), (47466, 2225), (53411, 0),
  (55969, 0), (56058, 0), (58682, 2245), (58730, 0), (58954, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X0Y0_check. -/
theorem Z0Split75A2X0Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X0Y0_pairs. -/
theorem Z0Split75A2X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A2X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X0_pairs. -/
theorem Z0Split75A2X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A2X1Y0Certs : List (Nat × Nat) := [
  (1152, 2173), (30532, 2163), (33494, 0), (35107, 0), (35179, 2270),
  (39255, 0), (40320, 0), (41288, 0), (41816, 0), (42344, 2230),
  (42827, 0), (43709, 2214), (45450, 2249), (50387, 0), (50514, 0),
  (56117, 0), (56256, 2220), (58002, 2256)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X1Y0_check. -/
theorem Z0Split75A2X1Y0_check : checkGrid m4TZ0 censusZ0 3 768556269 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A2X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X1Y0_pairs. -/
theorem Z0Split75A2X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 768556269 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A2X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A2X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2X1_pairs. -/
theorem Z0Split75A2X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A2X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A2_pairs. -/
theorem Z0Split75A2_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 768556269) = 4 →
      sweepAccept m4TZ0 3 x y 768556269 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split75A2X0_pairs x hx y hy hw
  · exact Z0Split75A2X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A3X0Y0Certs : List (Nat × Nat) := [
  (6022, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X0Y0_check. -/
theorem Z0Split75A3X0Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X0Y0_pairs. -/
theorem Z0Split75A3X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A3X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X0_pairs. -/
theorem Z0Split75A3X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split75A3X1Y0Certs : List (Nat × Nat) := [
  (3832, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X1Y0_check. -/
theorem Z0Split75A3X1Y0_check : checkGrid m4TZ0 censusZ0 3 1002105754 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A3X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X1Y0_pairs. -/
theorem Z0Split75A3X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 3 1002105754 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns) Z0Split75A3X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 3 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M3LeftColumns Z0M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split75A3X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3X1_pairs. -/
theorem Z0Split75A3X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split75A3X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75A3_pairs. -/
theorem Z0Split75A3_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 3 x y 1002105754) = 4 →
      sweepAccept m4TZ0 3 x y 1002105754 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split75A3X0_pairs x hx y hy hw
  · exact Z0Split75A3X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split75_check. -/
theorem Z0Split75_check : checkSplit m4TZ0 (3, 1, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 376821623, 768556269, 1002105754
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact Z0Split75A0_pairs x hx y hy hw
    · exact Z0Split75A1_pairs x hx y hy hw
    · exact Z0Split75A2_pairs x hx y hy hw
    · exact Z0Split75A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y0Certs : List (Nat × Nat) := [
  (296, 340), (15496, 104), (24850, 304), (27139, 333), (34837, 290),
  (40568, 155), (42179, 346), (47123, 291), (56546, 211), (64889, 303),
  (74981, 367), (75785, 287), (79970, 362), (83101, 330), (83191, 388),
  (85976, 403), (87215, 344), (92690, 350), (95794, 285), (102008, 183),
  (102053, 214), (102283, 368)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y0_check. -/
theorem Z0Split76A0X0Y0_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y0_pairs. -/
theorem Z0Split76A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y1Certs : List (Nat × Nat) := [
  (2723, 527), (7386, 518), (9132, 489), (20628, 456), (21304, 432),
  (46401, 522), (65758, 460), (68976, 449), (68990, 452), (69108, 513),
  (83237, 529), (86783, 508)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y1_check. -/
theorem Z0Split76A0X0Y1_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y1_pairs. -/
theorem Z0Split76A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split76A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y2Certs : List (Nat × Nat) := [
  (733, 674), (2792, 774), (6387, 786), (9919, 773), (10201, 747),
  (14915, 640), (20298, 779), (36772, 750), (43886, 712), (44385, 823),
  (47175, 766), (54865, 684), (55508, 681), (59042, 667), (62207, 824),
  (63110, 792), (67503, 686), (68417, 656)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y2_check. -/
theorem Z0Split76A0X0Y2_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y2_pairs. -/
theorem Z0Split76A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y2Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split76A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y3Certs : List (Nat × Nat) := [
  (1835, 940), (8209, 927), (8802, 841), (17743, 883), (20317, 981),
  (57122, 984), (58217, 929), (85481, 971), (92626, 936)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y3_check. -/
theorem Z0Split76A0X0Y3_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y3_pairs. -/
theorem Z0Split76A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y3Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split76A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y4Certs : List (Nat × Nat) := [
  (2694, 1164), (15880, 1234), (19446, 1070), (19552, 1116), (23020, 1163),
  (36932, 1100), (40507, 1190), (42127, 1037), (56697, 1065), (62999, 1068),
  (80862, 1045), (84614, 1241), (97807, 1051), (118767, 1110), (122319, 1208)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y4_check. -/
theorem Z0Split76A0X0Y4_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y4_pairs. -/
theorem Z0Split76A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y4Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split76A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y5Certs : List (Nat × Nat) := [
  (11718, 1373), (20873, 1394), (26896, 1371), (27073, 1321), (30076, 1441),
  (31362, 1395), (31402, 1413), (41266, 1379), (46386, 1311), (52220, 1338),
  (61848, 1320), (61864, 1326), (62295, 1405)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y5_check. -/
theorem Z0Split76A0X0Y5_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y5_pairs. -/
theorem Z0Split76A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y5Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split76A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y6Certs : List (Nat × Nat) := [
  (5678, 1549), (24619, 1463), (26982, 1551), (35966, 1537), (63348, 1473)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y6_check. -/
theorem Z0Split76A0X0Y6_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y6_pairs. -/
theorem Z0Split76A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y6Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split76A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y7Certs : List (Nat × Nat) := [
  (3390, 1638), (37006, 1710), (37235, 1659), (37356, 1721), (55196, 1707),
  (60525, 1605), (61853, 1615), (65480, 1644), (70097, 1679), (74260, 1646),
  (80450, 1651)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y7_check. -/
theorem Z0Split76A0X0Y7_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y7_pairs. -/
theorem Z0Split76A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y7Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split76A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y8Certs : List (Nat × Nat) := [
  (9595, 1794), (35191, 1784), (44341, 1792), (63740, 1843), (76380, 1850),
  (81091, 1750)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y8_check. -/
theorem Z0Split76A0X0Y8_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y8_pairs. -/
theorem Z0Split76A0X0Y8_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y8Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk8
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z0Split76A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y9Certs : List (Nat × Nat) := [
  (2773, 1993), (16988, 2073), (27612, 1950), (28094, 1991), (67345, 1970),
  (68115, 1977), (71133, 1973), (82736, 2057), (85121, 1974), (87310, 2081),
  (88510, 1968)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y9_check. -/
theorem Z0Split76A0X0Y9_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y9_pairs. -/
theorem Z0Split76A0X0Y9_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y9Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk9
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z0Split76A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X0Y10Certs : List (Nat × Nat) := [
  (6015, 2285), (23158, 2110), (32096, 2117), (33188, 2261), (36769, 2221),
  (45905, 2118), (48367, 2130), (73955, 2136), (83422, 2202), (98636, 2314),
  (98884, 2219)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y10_check. -/
theorem Z0Split76A0X0Y10_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0Y10_pairs. -/
theorem Z0Split76A0X0Y10_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X0Y10Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk0 masks3S512Chunk10
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z0Split76A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X0_pairs. -/
theorem Z0Split76A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z0Split76A0X0Y0_pairs x hx y hy hw
  · exact Z0Split76A0X0Y1_pairs x hx y hy hw
  · exact Z0Split76A0X0Y2_pairs x hx y hy hw
  · exact Z0Split76A0X0Y3_pairs x hx y hy hw
  · exact Z0Split76A0X0Y4_pairs x hx y hy hw
  · exact Z0Split76A0X0Y5_pairs x hx y hy hw
  · exact Z0Split76A0X0Y6_pairs x hx y hy hw
  · exact Z0Split76A0X0Y7_pairs x hx y hy hw
  · exact Z0Split76A0X0Y8_pairs x hx y hy hw
  · exact Z0Split76A0X0Y9_pairs x hx y hy hw
  · exact Z0Split76A0X0Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y0Certs : List (Nat × Nat) := [
  (7178, 365), (29150, 107), (40778, 309), (46397, 409), (47323, 52),
  (59117, 401), (61571, 219), (67607, 296), (69711, 185), (70105, 123),
  (75129, 133), (75587, 150)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y0_check. -/
theorem Z0Split76A0X1Y0_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y0_pairs. -/
theorem Z0Split76A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk0
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z0Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y1Certs : List (Nat × Nat) := [
  (8537, 551), (13295, 586), (14767, 598), (26716, 430), (27845, 454),
  (28779, 564)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y1_check. -/
theorem Z0Split76A0X1Y1_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y1_pairs. -/
theorem Z0Split76A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y1Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk1
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z0Split76A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y2Certs : List (Nat × Nat) := [
  (1770, 721), (4033, 711), (10666, 812), (12425, 694), (13051, 678),
  (13140, 762), (14366, 685), (14939, 650), (16762, 788), (21649, 797),
  (34329, 817), (34470, 702), (38866, 818), (41150, 634), (43675, 795)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y2_check. -/
theorem Z0Split76A0X1Y2_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y2_pairs. -/
theorem Z0Split76A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y2Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk2
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z0Split76A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y3Certs : List (Nat × Nat) := [
  (1201, 840), (10171, 895), (16072, 867), (16330, 989), (18565, 888),
  (19056, 947), (19758, 887), (20677, 968), (20702, 976), (47946, 998),
  (50273, 966), (53869, 964), (64173, 896)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y3_check. -/
theorem Z0Split76A0X1Y3_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y3_pairs. -/
theorem Z0Split76A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y3Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk3
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z0Split76A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y4Certs : List (Nat × Nat) := [
  (1720, 1162), (1890, 1259), (5962, 1103), (9496, 1180), (23439, 1118),
  (24817, 1092), (42219, 1083), (43616, 1061), (52693, 1255), (56480, 1194),
  (80894, 1064)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y4_check. -/
theorem Z0Split76A0X1Y4_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y4_pairs. -/
theorem Z0Split76A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y4Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk4
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z0Split76A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y5Certs : List (Nat × Nat) := [
  (762, 1412), (918, 1357), (4257, 1363), (14329, 1438), (15662, 1408),
  (25985, 1328), (37168, 1400), (41347, 1418), (42540, 1323), (45837, 1318)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y5_check. -/
theorem Z0Split76A0X1Y5_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y5_pairs. -/
theorem Z0Split76A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y5Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk5
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z0Split76A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y6Certs : List (Nat × Nat) := [
  (1065, 1508), (20461, 1481), (30453, 1505), (31517, 1462), (39345, 1472),
  (42234, 1529)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y6_check. -/
theorem Z0Split76A0X1Y6_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y6_pairs. -/
theorem Z0Split76A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y6Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk6
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z0Split76A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y7Certs : List (Nat × Nat) := [
  (16913, 1580), (21237, 1622), (30198, 1714), (37706, 1576), (42248, 1726),
  (43800, 1692)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y7_check. -/
theorem Z0Split76A0X1Y7_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y7_pairs. -/
theorem Z0Split76A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y7Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk7
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z0Split76A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y8Certs : List (Nat × Nat) := [
  (10720, 1835), (25856, 1870), (36964, 1789), (37178, 1908), (42982, 1822),
  (47039, 1745), (53915, 1848), (59621, 1903)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y8_check. -/
theorem Z0Split76A0X1Y8_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y8_pairs. -/
theorem Z0Split76A0X1Y8_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y8Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk8
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z0Split76A0X1Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y9Certs : List (Nat × Nat) := [
  (39843, 2010), (47776, 2003), (60481, 1939), (62820, 1975)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y9_check. -/
theorem Z0Split76A0X1Y9_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y9_pairs. -/
theorem Z0Split76A0X1Y9_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y9Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk9
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z0Split76A0X1Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split76A0X1Y10Certs : List (Nat × Nat) := [
  (16158, 2278), (19772, 2255), (30091, 2129), (63414, 2151), (67615, 2215),
  (67801, 2320)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y10_check. -/
theorem Z0Split76A0X1Y10_check : checkGrid m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1Y10_pairs. -/
theorem Z0Split76A0X1Y10_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z0M2LeftColumns Z0M2RightColumns) Z0Split76A0X1Y10Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M2Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ0 2 outerMasks2S256Chunk1 masks3S512Chunk10
      Z0M2LeftColumns Z0M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(Z0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z0M2Left_eq
    · exact Z0M2Right_eq
    · intro x hx
      exact Z0M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M2Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z0Split76A0X1Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0X1_pairs. -/
theorem Z0Split76A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z0Split76A0X1Y0_pairs x hx y hy hw
  · exact Z0Split76A0X1Y1_pairs x hx y hy hw
  · exact Z0Split76A0X1Y2_pairs x hx y hy hw
  · exact Z0Split76A0X1Y3_pairs x hx y hy hw
  · exact Z0Split76A0X1Y4_pairs x hx y hy hw
  · exact Z0Split76A0X1Y5_pairs x hx y hy hw
  · exact Z0Split76A0X1Y6_pairs x hx y hy hw
  · exact Z0Split76A0X1Y7_pairs x hx y hy hw
  · exact Z0Split76A0X1Y8_pairs x hx y hy hw
  · exact Z0Split76A0X1Y9_pairs x hx y hy hw
  · exact Z0Split76A0X1Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76A0_pairs. -/
theorem Z0Split76A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ0 2 x y 0) = 3 →
      sweepAccept m4TZ0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split76A0X0_pairs x hx y hy hw
  · exact Z0Split76A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split76_check. -/
theorem Z0Split76_check : checkSplit m4TZ0 (3, 2, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z0M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X0Y0Certs : List (Nat × Nat) := [
  (9316, 771), (10680, 1049), (18178, 1642), (22067, 1500), (29359, 920),
  (44735, 1781), (49517, 1768), (76345, 939), (79196, 127), (81601, 1150),
  (85811, 459)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X0Y0_check. -/
theorem Z0Split77A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X0Y0_pairs. -/
theorem Z0Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk0 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X0_pairs. -/
theorem Z0Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X1Y0Certs : List (Nat × Nat) := [
  (7687, 1365), (11215, 1619), (12561, 1940), (17855, 106), (31818, 249),
  (32735, 437), (44949, 561), (45250, 78), (58691, 2032), (77665, 1031),
  (83992, 173), (100311, 1157)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X1Y0_check. -/
theorem Z0Split77A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X1Y0_pairs. -/
theorem Z0Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk1 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X1_pairs. -/
theorem Z0Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X2Y0Certs : List (Nat × Nat) := [
  (2171, 2258), (3980, 255), (13365, 1493), (17111, 569), (25776, 441),
  (28185, 1666), (32181, 2199), (34640, 1276), (41748, 2170), (81892, 445)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X2Y0_check. -/
theorem Z0Split77A0X2Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X2Y0_pairs. -/
theorem Z0Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X2Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk2_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk2 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X2_pairs. -/
theorem Z0Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X3Y0Certs : List (Nat × Nat) := [
  (459, 125), (19175, 160), (20566, 487), (25127, 1584), (31408, 353),
  (33625, 510), (36028, 1760), (36257, 608), (37670, 1155), (43727, 986),
  (48059, 894)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X3Y0_check. -/
theorem Z0Split77A0X3Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X3Y0_pairs. -/
theorem Z0Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X3Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk3_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk3 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X3_pairs. -/
theorem Z0Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X4Y0Certs : List (Nat × Nat) := [
  (518, 339), (1983, 1062), (2376, 861), (24204, 1301), (29042, 1586),
  (31554, 1027), (32575, 1951), (38060, 924), (39671, 345), (40490, 159),
  (50101, 295)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X4Y0_check. -/
theorem Z0Split77A0X4Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X4Y0_pairs. -/
theorem Z0Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X4Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk4_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk4 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X4_pairs. -/
theorem Z0Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X5Y0Certs : List (Nat × Nat) := [
  (395, 2002), (3477, 2283), (10530, 364), (14841, 216), (17550, 594),
  (18925, 938), (19231, 382), (35511, 1297), (40357, 1603), (45721, 204),
  (47682, 1185), (48332, 207), (69524, 1761)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X5Y0_check. -/
theorem Z0Split77A0X5Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X5Y0_pairs. -/
theorem Z0Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X5Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk5_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk5 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X5_pairs. -/
theorem Z0Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X6Y0Certs : List (Nat × Nat) := [
  (620, 790), (6629, 407), (26031, 1787), (27294, 1547), (29174, 147),
  (30895, 79), (33629, 524), (44475, 423), (45139, 1590), (47985, 530),
  (56224, 434), (68109, 1101), (77962, 387), (80840, 1782)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X6Y0_check. -/
theorem Z0Split77A0X6Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X6Y0_pairs. -/
theorem Z0Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X6Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk6_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk6 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X6_pairs. -/
theorem Z0Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X7Y0Certs : List (Nat × Nat) := [
  (10004, 2313), (11264, 1966), (18857, 607), (34738, 1869), (37647, 1036),
  (42594, 2023), (47356, 1902), (48989, 1207), (52369, 700), (54673, 1423),
  (63297, 944), (65990, 1460), (72521, 1478), (75925, 1032), (76502, 1915),
  (84261, 1461), (86829, 1173)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X7Y0_check. -/
theorem Z0Split77A0X7Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X7Y0_pairs. -/
theorem Z0Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X7Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk7_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk7 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X7_pairs. -/
theorem Z0Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X8Y0Certs : List (Nat × Nat) := [
  (1101, 1024), (5935, 1305), (13293, 1063), (13934, 82), (17923, 351),
  (20338, 1575), (78958, 960)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X8Y0_check. -/
theorem Z0Split77A0X8Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X8Y0_pairs. -/
theorem Z0Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X8Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk8_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk8 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X8_pairs. -/
theorem Z0Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X9Y0Certs : List (Nat × Nat) := [
  (7480, 343), (12682, 274), (33830, 1593), (46264, 628), (50566, 427),
  (51869, 408), (55045, 1033), (61853, 338), (71962, 801), (74197, 1086),
  (78719, 2150), (79010, 1275), (80839, 1778), (89429, 1140), (92173, 1961),
  (96024, 1545)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X9Y0_check. -/
theorem Z0Split77A0X9Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X9Y0_pairs. -/
theorem Z0Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X9Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk9_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk9 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X9_pairs. -/
theorem Z0Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X10Y0Certs : List (Nat × Nat) := [
  (3741, 1159), (9904, 1592), (16506, 2105), (17460, 237), (29130, 2155),
  (35262, 132), (37164, 814), (44937, 519), (49863, 1254), (51451, 486),
  (51957, 839), (77435, 51), (84548, 639), (86462, 1585), (92344, 491),
  (95636, 1834), (96696, 497)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X10Y0_check. -/
theorem Z0Split77A0X10Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X10Y0_pairs. -/
theorem Z0Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X10Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk10_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk10 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X10_pairs. -/
theorem Z0Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X11Y0_check. -/
theorem Z0Split77A0X11Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X11Y0_pairs. -/
theorem Z0Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X11Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk11_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk11 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X11_pairs. -/
theorem Z0Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X12Y0Certs : List (Nat × Nat) := [
  (7691, 1403), (9460, 1568), (9960, 1972), (15603, 1938), (17010, 203),
  (29789, 890), (37702, 1366), (40973, 335), (46478, 1809), (50567, 429),
  (63502, 2207), (65196, 1941), (68390, 386), (70952, 206), (74201, 1114),
  (90257, 917), (90590, 438), (95952, 1120), (107229, 935)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X12Y0_check. -/
theorem Z0Split77A0X12Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X12Y0_pairs. -/
theorem Z0Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X12Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk12_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk12 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X12_pairs. -/
theorem Z0Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X13Y0Certs : List (Nat × Nat) := [
  (16297, 865), (19131, 2200)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X13Y0_check. -/
theorem Z0Split77A0X13Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X13Y0_pairs. -/
theorem Z0Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X13Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk13_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk13 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X13_pairs. -/
theorem Z0Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X14Y0Certs : List (Nat × Nat) := [
  (8592, 1570), (22659, 180), (27035, 253), (27944, 406), (42538, 1643),
  (43554, 223), (50212, 799), (53966, 129)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X14Y0_check. -/
theorem Z0Split77A0X14Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X14Y0_pairs. -/
theorem Z0Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X14Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk14_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk14 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X14_pairs. -/
theorem Z0Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X15Y0Certs : List (Nat × Nat) := [
  (17137, 740)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X15Y0_check. -/
theorem Z0Split77A0X15Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X15Y0_pairs. -/
theorem Z0Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X15Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk15_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk15 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X15_pairs. -/
theorem Z0Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X16Y0Certs : List (Nat × Nat) := [
  (3173, 503), (13433, 1946), (25136, 1627), (25774, 433), (31504, 785),
  (41482, 636), (53016, 1944), (66853, 1421), (74075, 493), (93096, 63),
  (94970, 550), (98959, 921), (100259, 893), (106039, 1591)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X16Y0_check. -/
theorem Z0Split77A0X16Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X16Y0_pairs. -/
theorem Z0Split77A0X16Y0_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X16Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk16_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk16 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk16_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X16_pairs. -/
theorem Z0Split77A0X16_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X17Y0Certs : List (Nat × Nat) := [
  (347, 1683), (5401, 770), (13589, 404), (16712, 778), (17342, 1914),
  (19130, 2193), (29935, 1746)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X17Y0_check. -/
theorem Z0Split77A0X17Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X17Y0_pairs. -/
theorem Z0Split77A0X17Y0_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X17Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk17_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk17 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk17_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X17_pairs. -/
theorem Z0Split77A0X17_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X18Y0Certs : List (Nat × Nat) := [
  (13171, 485), (15620, 2001), (15859, 856), (26046, 1942), (27109, 548),
  (31623, 1455), (34812, 80), (35831, 648), (45270, 149), (48842, 488),
  (52326, 496), (52961, 1569), (69489, 1546), (80709, 1029), (84273, 1504),
  (85876, 768), (93519, 2240), (98961, 926)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X18Y0_check. -/
theorem Z0Split77A0X18Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X18Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X18Y0_pairs. -/
theorem Z0Split77A0X18Y0_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X18Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk18_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk18 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk18_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X18Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X18_pairs. -/
theorem Z0Split77A0X18_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X18Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X19Y0Certs : List (Nat × Nat) := [
  (350, 1719), (6581, 233), (8300, 156), (20665, 937), (22061, 1479),
  (30466, 98), (40561, 425), (46180, 279)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X19Y0_check. -/
theorem Z0Split77A0X19Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X19Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X19Y0_pairs. -/
theorem Z0Split77A0X19Y0_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X19Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk19_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk19 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk19_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X19Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X19_pairs. -/
theorem Z0Split77A0X19_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X19Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X20Y0Certs : List (Nat × Nat) := [
  (763, 1574), (16133, 178), (17645, 1075), (24159, 1026), (26585, 212),
  (40282, 1161), (41099, 891), (42248, 221), (43227, 651), (62006, 1034),
  (63294, 934), (72070, 1393), (86601, 172), (92948, 1377), (102201, 2104),
  (102260, 157)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X20Y0_check. -/
theorem Z0Split77A0X20Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X20Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X20Y0_pairs. -/
theorem Z0Split77A0X20Y0_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X20Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk20_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk20 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk20_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X20Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X20_pairs. -/
theorem Z0Split77A0X20_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X20Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split77A0X21Y0Certs : List (Nat × Nat) := [
  (241, 1054), (472, 174), (21204, 1543), (22037, 1336), (39260, 436),
  (43830, 1577), (50752, 1368), (55225, 2123)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X21Y0_check. -/
theorem Z0Split77A0X21Y0_check : checkGrid m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X21Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X21Y0_pairs. -/
theorem Z0Split77A0X21Y0_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split77A0X21Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk21_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S256Chunk21 masks2S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk21_bound
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
      exact Z0M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z0Split77A0X21Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0X21_pairs. -/
theorem Z0Split77A0X21_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split77A0X21Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77A0_pairs. -/
theorem Z0Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 3 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact Z0Split77A0X0_pairs x hx y hy hw
  · exact Z0Split77A0X1_pairs x hx y hy hw
  · exact Z0Split77A0X2_pairs x hx y hy hw
  · exact Z0Split77A0X3_pairs x hx y hy hw
  · exact Z0Split77A0X4_pairs x hx y hy hw
  · exact Z0Split77A0X5_pairs x hx y hy hw
  · exact Z0Split77A0X6_pairs x hx y hy hw
  · exact Z0Split77A0X7_pairs x hx y hy hw
  · exact Z0Split77A0X8_pairs x hx y hy hw
  · exact Z0Split77A0X9_pairs x hx y hy hw
  · exact Z0Split77A0X10_pairs x hx y hy hw
  · exact Z0Split77A0X11_pairs x hx y hy hw
  · exact Z0Split77A0X12_pairs x hx y hy hw
  · exact Z0Split77A0X13_pairs x hx y hy hw
  · exact Z0Split77A0X14_pairs x hx y hy hw
  · exact Z0Split77A0X15_pairs x hx y hy hw
  · exact Z0Split77A0X16_pairs x hx y hy hw
  · exact Z0Split77A0X17_pairs x hx y hy hw
  · exact Z0Split77A0X18_pairs x hx y hy hw
  · exact Z0Split77A0X19_pairs x hx y hy hw
  · exact Z0Split77A0X20_pairs x hx y hy hw
  · exact Z0Split77A0X21_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split77_check. -/
theorem Z0Split77_check : checkSplit m4TZ0 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split78A0X0Y0Certs : List (Nat × Nat) := [
  (646, 483), (1837, 116), (4790, 836), (5424, 1293), (5486, 1562),
  (6430, 197), (6981, 904), (7132, 1018), (8881, 13), (9500, 833),
  (11608, 1925), (11743, 321), (14616, 92), (15585, 413), (17449, 736),
  (18784, 57), (20185, 1444), (20446, 480), (22057, 110), (22443, 47),
  (22565, 76), (22729, 727), (24286, 482), (24520, 198), (25933, 322),
  (26011, 17), (26140, 201), (26465, 72), (26666, 1563), (30484, 56),
  (32005, 1449), (36135, 419), (36668, 138), (36919, 735), (37398, 615),
  (40855, 1446), (42912, 265), (43666, 481), (44134, 60), (44451, 903),
  (47435, 75), (47602, 1022), (48285, 417), (48624, 1290), (50859, 168),
  (52918, 1930), (53662, 1021), (54519, 169), (57283, 315), (57907, 117),
  (58090, 200), (58254, 1288), (59461, 20), (60532, 1023)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X0Y0_check. -/
theorem Z0Split78A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X0Y0_pairs. -/
theorem Z0Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split78A0X0Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X0_pairs. -/
theorem Z0Split78A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split78A0X1Y0Certs : List (Nat × Nat) := [
  (434, 380), (2137, 118), (3789, 163), (6088, 1936), (12831, 911),
  (12968, 144), (13694, 376), (13974, 1287), (14700, 2), (17745, 422),
  (20740, 196), (20761, 19), (21026, 1566), (22101, 909), (22448, 143),
  (22593, 48), (27244, 62), (27904, 59), (29023, 312), (29216, 1565),
  (30765, 414), (31636, 478), (34623, 45), (34819, 732), (37436, 1567),
  (38204, 377), (38672, 28), (45781, 15), (45843, 41), (46310, 832),
  (48952, 1020), (49235, 71), (50109, 171), (50743, 320), (51759, 165),
  (53569, 728), (53823, 44), (53855, 73), (56121, 905), (59497, 115),
  (59814, 1295)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X1Y0_check. -/
theorem Z0Split78A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split78A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X1Y0_pairs. -/
theorem Z0Split78A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split78A0X1Y0Certs
  · exact censusZ0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ0 0 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z0Split78A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0X1_pairs. -/
theorem Z0Split78A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split78A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78A0_pairs. -/
theorem Z0Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 4 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split78A0X0_pairs x hx y hy hw
  · exact Z0Split78A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split78_check. -/
theorem Z0Split78_check : checkSplit m4TZ0 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z0Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X0Y0_check. -/
theorem Z0Split79A0X0Y0_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X0Y0_pairs. -/
theorem Z0Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split79A0X0Y0Certs
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
  · exact Z0Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X0_pairs. -/
theorem Z0Split79A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z0Split79A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X1Y0_check. -/
theorem Z0Split79A0X1Y0_check : checkGrid m4TZ0 censusZ0 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split79A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X1Y0_pairs. -/
theorem Z0Split79A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  apply checkGrid_sound m4TZ0 censusZ0 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z0M0LeftColumns Z0M0RightColumns) Z0Split79A0X1Y0Certs
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
  · exact Z0Split79A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0X1_pairs. -/
theorem Z0Split79A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z0Split79A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79A0_pairs. -/
theorem Z0Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ0 0 x y 0) = 5 →
      sweepAccept m4TZ0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z0Split79A0X0_pairs x hx y hy hw
  · exact Z0Split79A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0Split79_check. -/
theorem Z0Split79_check : checkSplit m4TZ0 (3, 5, 0, 0) = true := by
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
    · exact Z0Split79A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

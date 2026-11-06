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
def Z1Split48A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0X0Y0_check. -/
theorem Z1Split48A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split48A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0X0Y0_pairs. -/
theorem Z1Split48A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split48A0X0Y0Certs
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
  · exact Z1Split48A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0X0_pairs. -/
theorem Z1Split48A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split48A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split48A0_pairs. -/
theorem Z1Split48A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 5 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split48A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split48_check. -/
theorem Z1Split48_check : checkSplit m4TZ1 (5, 1, 0, 2) = true := by
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
    · exact Z1Split48A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split49A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0X0Y0_check. -/
theorem Z1Split49A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split49A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0X0Y0_pairs. -/
theorem Z1Split49A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 6
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split49A0X0Y0Certs
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
  · exact Z1Split49A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0X0_pairs. -/
theorem Z1Split49A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split49A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split49A0_pairs. -/
theorem Z1Split49A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 6 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split49A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split49_check. -/
theorem Z1Split49_check : checkSplit m4TZ1 (6, 0, 0, 2) = true := by
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
    · exact Z1Split49A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split50A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0X0Y0_check. -/
theorem Z1Split50A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split50A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0X0Y0_pairs. -/
theorem Z1Split50A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 8 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split50A0X0Y0Certs
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
  · exact Z1Split50A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0X0_pairs. -/
theorem Z1Split50A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 8 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split50A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split50A0_pairs. -/
theorem Z1Split50A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 8 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split50A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split50_check. -/
theorem Z1Split50_check : checkSplit m4TZ1 (0, 0, 8, 3) = true := by
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
    · exact Z1Split50A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split51A0X0Y0Certs : List (Nat × Nat) := [
  (1, 2033), (3, 2021), (4, 2907), (5, 1155), (7, 2886),
  (8, 1153), (9, 2791), (10, 2079), (13, 2290), (14, 2077),
  (15, 1712), (16, 2914), (19, 1282), (20, 2888), (21, 1298),
  (22, 2748), (24, 1765), (25, 2304), (26, 2165), (28, 2660)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0X0Y0_check. -/
theorem Z1Split51A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split51A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0X0Y0_pairs. -/
theorem Z1Split51A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split51A0X0Y0Certs
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
  · exact Z1Split51A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0X0_pairs. -/
theorem Z1Split51A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split51A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split51A0_pairs. -/
theorem Z1Split51A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split51A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split51_check. -/
theorem Z1Split51_check : checkSplit m4TZ1 (0, 1, 7, 3) = true := by
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
    · exact Z1Split51A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split52A0X0Y0Certs : List (Nat × Nat) := [
  (4, 1104), (25, 2005), (33, 520), (55, 1558), (61, 1581),
  (77, 3224), (87, 2864), (101, 1154), (138, 2531), (148, 2464),
  (170, 3225), (186, 1797), (206, 2078), (253, 3226), (259, 3231),
  (271, 3062), (297, 1775), (322, 2910), (351, 845), (353, 3228),
  (363, 3209), (404, 2847), (408, 877), (412, 3232), (424, 3074)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0X0Y0_check. -/
theorem Z1Split52A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split52A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0X0Y0_pairs. -/
theorem Z1Split52A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split52A0X0Y0Certs
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
  · exact Z1Split52A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0X0_pairs. -/
theorem Z1Split52A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split52A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split52A0_pairs. -/
theorem Z1Split52A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split52A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split52_check. -/
theorem Z1Split52_check : checkSplit m4TZ1 (0, 2, 6, 3) = true := by
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
    · exact Z1Split52A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split53A0X0Y0Certs : List (Nat × Nat) := [
  (21, 3127), (180, 2540), (221, 2539), (235, 3053), (237, 2529),
  (275, 3121), (281, 3140), (695, 3194), (748, 3220), (757, 1576),
  (817, 3199), (831, 1562), (833, 3207), (873, 3221), (882, 3230),
  (884, 728), (888, 3227), (954, 2474), (964, 2520), (1786, 3139),
  (1826, 3037), (1828, 2538), (1832, 3055), (1839, 3078), (1918, 873),
  (1924, 3214), (1930, 3193), (1941, 2441)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0Y0_check. -/
theorem Z1Split53A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split53A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0Y0_pairs. -/
theorem Z1Split53A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split53A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z1M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z1Split53A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split53A0X0Y1Certs : List (Nat × Nat) := [
  (902, 3117), (956, 2536), (967, 3075), (969, 2511), (978, 3132),
  (1039, 1583), (1043, 3205), (1048, 3223), (1049, 743), (1060, 1589),
  (1065, 744), (1154, 3134), (1165, 3073), (1171, 1517), (1647, 2444),
  (1691, 3077), (1696, 2526), (1766, 1592), (1768, 3191), (1777, 844),
  (1785, 1563), (1789, 3198), (1800, 2388), (1889, 2473), (1894, 2528),
  (1895, 2990), (1900, 3208), (1901, 1591), (1983, 2407), (1992, 3061),
  (1998, 1556), (2004, 2463)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0Y1_check. -/
theorem Z1Split53A0X0Y1_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M3LeftColumns Z1M3RightColumns) Z1Split53A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0Y1_pairs. -/
theorem Z1Split53A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M3LeftColumns Z1M3RightColumns) Z1Split53A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z1M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z1Split53A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0X0_pairs. -/
theorem Z1Split53A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split53A0X0Y0_pairs x hx y hy hw
  · exact Z1Split53A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split53A0_pairs. -/
theorem Z1Split53A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split53A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split53_check. -/
theorem Z1Split53_check : checkSplit m4TZ1 (0, 3, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split53A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y0Certs : List (Nat × Nat) := [
  (320, 258), (351, 293), (661, 359), (1319, 514), (1758, 581)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y0_check. -/
theorem Z1Split54A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y0_pairs. -/
theorem Z1Split54A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk0_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk0_bound y hy)
  · exact Z1Split54A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y1Certs : List (Nat × Nat) := [
  (371, 653), (543, 667), (781, 734), (795, 736), (797, 737),
  (835, 740), (837, 741)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y1_check. -/
theorem Z1Split54A0X0Y1_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y1_pairs. -/
theorem Z1Split54A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk1_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk1_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk1_bound y hy)
  · exact Z1Split54A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y2Certs : List (Nat × Nat) := [
  (180, 826), (182, 827), (275, 842), (277, 843), (681, 869),
  (695, 871), (697, 872), (741, 874), (949, 920), (1459, 985)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y2_check. -/
theorem Z1Split54A0X0Y2_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y2_pairs. -/
theorem Z1Split54A0X0Y2_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk2
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y2Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk2_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk2
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk2_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk2_bound y hy)
  · exact Z1Split54A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y3Certs : List (Nat × Nat) := [
  (144, 1044), (499, 1082), (1069, 1147)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y3_check. -/
theorem Z1Split54A0X0Y3_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y3_pairs. -/
theorem Z1Split54A0X0Y3_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk3
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y3Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk3_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk3
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk3_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk3_bound y hy)
  · exact Z1Split54A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y4Certs : List (Nat × Nat) := [
  (149, 1208), (1235, 1296)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y4_check. -/
theorem Z1Split54A0X0Y4_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y4_pairs. -/
theorem Z1Split54A0X0Y4_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk4
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y4Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk4_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk4
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk4_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk4_bound y hy)
  · exact Z1Split54A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y5Certs : List (Nat × Nat) := [
  (48, 1328), (641, 1386), (1180, 1418), (1517, 1443)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y5_check. -/
theorem Z1Split54A0X0Y5_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y5_pairs. -/
theorem Z1Split54A0X0Y5_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk5
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y5Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk5_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk5
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk5_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk5_bound y hy)
  · exact Z1Split54A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y6Certs : List (Nat × Nat) := [
  (21, 1481), (180, 1504), (221, 1511), (235, 1515), (275, 1519),
  (281, 1520), (735, 1554), (741, 1557), (746, 1561), (833, 1571),
  (871, 1574), (877, 1575), (884, 1578), (888, 1580), (893, 1582),
  (954, 1587), (958, 1588)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y6_check. -/
theorem Z1Split54A0X0Y6_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y6_pairs. -/
theorem Z1Split54A0X0Y6_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk6
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y6Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk6_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk6
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk6_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk6_bound y hy)
  · exact Z1Split54A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y7Certs : List (Nat × Nat) := [
  (377, 1690), (612, 1719), (1721, 1822)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y7_check. -/
theorem Z1Split54A0X0Y7_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y7_pairs. -/
theorem Z1Split54A0X0Y7_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk7
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y7Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk7_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk7
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk7_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk7_bound y hy)
  · exact Z1Split54A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y8Certs : List (Nat × Nat) := [
  (63, 1866), (645, 1922), (1177, 1952), (1449, 1976)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y8_check. -/
theorem Z1Split54A0X0Y8_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y8_pairs. -/
theorem Z1Split54A0X0Y8_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk8,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk8
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk8
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y8Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk8_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk8
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk8_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk8_bound y hy)
  · exact Z1Split54A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y9Certs : List (Nat × Nat) := [
  (205, 2067)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y9_check. -/
theorem Z1Split54A0X0Y9_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y9_pairs. -/
theorem Z1Split54A0X0Y9_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk9,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk9
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk9
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y9Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk9_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk9
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk9_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk9_bound y hy)
  · exact Z1Split54A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y10Certs : List (Nat × Nat) := [
  (19, 2107), (338, 2155), (1718, 2261)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y10_check. -/
theorem Z1Split54A0X0Y10_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y10_pairs. -/
theorem Z1Split54A0X0Y10_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk10,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk10
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk10
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y10Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk10_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk10
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk10_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk10_bound y hy)
  · exact Z1Split54A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y11Certs : List (Nat × Nat) := [
  (83, 2283), (123, 2286), (179, 2288), (232, 2294), (390, 2315)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y11_check. -/
theorem Z1Split54A0X0Y11_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y11Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y11_pairs. -/
theorem Z1Split54A0X0Y11_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk11,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk11
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk11
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y11Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk11_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk11
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk11_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk11_bound y hy)
  · exact Z1Split54A0X0Y11_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y12Certs : List (Nat × Nat) := [
  (166, 2384), (180, 2386), (182, 2387), (235, 2398), (237, 2399),
  (275, 2404), (277, 2405), (281, 2406), (681, 2431), (735, 2435),
  (737, 2436), (741, 2437), (746, 2439), (748, 2440), (831, 2452),
  (833, 2453), (882, 2460), (884, 2461), (952, 2468), (954, 2469),
  (963, 2470), (964, 2472), (1786, 2508), (1828, 2510), (1832, 2512),
  (1837, 2515), (1848, 2519), (1909, 2525), (1919, 2530), (1926, 2535),
  (1935, 2537)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y12_check. -/
theorem Z1Split54A0X0Y12_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y12Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y12_pairs. -/
theorem Z1Split54A0X0Y12_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk12,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk12
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk12
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y12Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk12_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk12
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk12_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk12_bound y hy)
  · exact Z1Split54A0X0Y12_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y13Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y13_check. -/
theorem Z1Split54A0X0Y13_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y13Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y13_pairs. -/
theorem Z1Split54A0X0Y13_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk13,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk13
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk13
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y13Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk13_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk13
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk13_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk13_bound y hy)
  · exact Z1Split54A0X0Y13_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y14Certs : List (Nat × Nat) := [
  (78, 2618), (404, 2656), (1374, 2732), (1440, 2735), (1521, 2739),
  (1724, 2764)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y14_check. -/
theorem Z1Split54A0X0Y14_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y14Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y14_pairs. -/
theorem Z1Split54A0X0Y14_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk14,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk14
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk14
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y14Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk14_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk14
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk14_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk14_bound y hy)
  · exact Z1Split54A0X0Y14_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y15Certs : List (Nat × Nat) := [
  (385, 2809), (489, 2821)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y15_check. -/
theorem Z1Split54A0X0Y15_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y15Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y15_pairs. -/
theorem Z1Split54A0X0Y15_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk15,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk15
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk15
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y15Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk15_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk15
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk15_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk15_bound y hy)
  · exact Z1Split54A0X0Y15_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y16Certs : List (Nat × Nat) := [
  (180, 2988), (221, 2998), (235, 3001), (277, 3004), (697, 3028),
  (737, 3032), (748, 3034), (752, 3036), (817, 3045), (831, 3048),
  (877, 3054), (884, 3058), (888, 3060), (954, 3070), (958, 3071),
  (963, 3072), (964, 3076), (1772, 3109), (1786, 3111), (1788, 3112),
  (1826, 3115), (1828, 3116), (1848, 3119), (1907, 3123), (1909, 3124),
  (1913, 3125), (1919, 3128), (1924, 3130), (1926, 3131), (1930, 3133),
  (1935, 3136)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y16_check. -/
theorem Z1Split54A0X0Y16_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y16Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y16_pairs. -/
theorem Z1Split54A0X0Y16_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk16,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk16
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk16
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y16Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk16_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk16
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk16_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk16_bound y hy)
  · exact Z1Split54A0X0Y16_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split54A0X0Y17Certs : List (Nat × Nat) := [
  (916, 3182), (956, 3187), (969, 3190), (978, 3192), (1037, 3196),
  (1043, 3197), (1049, 3200), (1056, 3204), (1071, 3213), (1160, 3219),
  (1172, 3229)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y17_check. -/
theorem Z1Split54A0X0Y17_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y17Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0Y17_pairs. -/
theorem Z1Split54A0X0Y17_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks4S2048Chunk17,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks0S256Chunk0 masks4S2048Chunk17
    (gridWords outerMasks0S256Chunk0 masks4S2048Chunk17
      Z1M0LeftColumns Z1M0RightColumns) Z1Split54A0X0Y17Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks4S2048Chunk17_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks0S256Chunk0 masks4S2048Chunk17
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks4S2048Chunk17_bound
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
      exact Z1M0Right_bound y (masks4S2048Chunk17_bound y hy)
  · exact Z1Split54A0X0Y17_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0X0_pairs. -/
theorem Z1Split54A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks4S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks4S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z1Split54A0X0Y0_pairs x hx y hy hw
  · exact Z1Split54A0X0Y1_pairs x hx y hy hw
  · exact Z1Split54A0X0Y2_pairs x hx y hy hw
  · exact Z1Split54A0X0Y3_pairs x hx y hy hw
  · exact Z1Split54A0X0Y4_pairs x hx y hy hw
  · exact Z1Split54A0X0Y5_pairs x hx y hy hw
  · exact Z1Split54A0X0Y6_pairs x hx y hy hw
  · exact Z1Split54A0X0Y7_pairs x hx y hy hw
  · exact Z1Split54A0X0Y8_pairs x hx y hy hw
  · exact Z1Split54A0X0Y9_pairs x hx y hy hw
  · exact Z1Split54A0X0Y10_pairs x hx y hy hw
  · exact Z1Split54A0X0Y11_pairs x hx y hy hw
  · exact Z1Split54A0X0Y12_pairs x hx y hy hw
  · exact Z1Split54A0X0Y13_pairs x hx y hy hw
  · exact Z1Split54A0X0Y14_pairs x hx y hy hw
  · exact Z1Split54A0X0Y15_pairs x hx y hy hw
  · exact Z1Split54A0X0Y16_pairs x hx y hy hw
  · exact Z1Split54A0X0Y17_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54A0_pairs. -/
theorem Z1Split54A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split54A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split54_check. -/
theorem Z1Split54_check : checkSplit m4TZ1 (0, 4, 4, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 4 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split54A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split55A0X0Y0Certs : List (Nat × Nat) := [
  (21, 110), (42, 138), (44, 140), (46, 143), (65, 162),
  (151, 248), (166, 285), (221, 330), (235, 344), (237, 345),
  (281, 360), (326, 404), (327, 408), (329, 411), (330, 415),
  (335, 420), (375, 452), (407, 475), (414, 489), (417, 494),
  (488, 553), (658, 655), (681, 691), (695, 703), (697, 706),
  (735, 724), (737, 725), (757, 739), (817, 791), (831, 801),
  (833, 802), (871, 819), (873, 821), (882, 836), (884, 838),
  (888, 839), (964, 876), (1002, 910), (1083, 953), (1084, 958),
  (1087, 963), (1088, 972), (1098, 981), (1189, 1042), (1258, 1085),
  (1261, 1096), (1263, 1098), (1270, 1108), (1274, 1117), (1334, 1176),
  (1431, 1230), (1544, 1313), (1743, 1421), (1788, 1480), (1828, 1502),
  (1839, 1510), (1843, 1514), (1909, 1546), (1913, 1547), (1918, 1553),
  (1924, 1569), (1941, 1585)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0Y0_check. -/
theorem Z1Split55A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split55A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0Y0_pairs. -/
theorem Z1Split55A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split55A0X0Y0Certs
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
  · exact Z1Split55A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split55A0X0Y1Certs : List (Nat × Nat) := [
  (4, 1642), (101, 1694), (225, 1776), (226, 1784), (229, 1790),
  (230, 1803), (246, 1817), (280, 1848), (405, 1918), (505, 1979),
  (511, 1992), (514, 1994), (523, 2012), (527, 2026), (601, 2112),
  (609, 2123), (789, 2235), (794, 2238), (895, 2321), (902, 2356),
  (973, 2397), (1043, 2433), (1048, 2434), (1060, 2451), (1065, 2456),
  (1066, 2459), (1154, 2504), (1160, 2507), (1165, 2509), (1166, 2514),
  (1171, 2524), (1277, 2605), (1285, 2614), (1498, 2758), (1529, 2781),
  (1533, 2783), (1586, 2848), (1590, 2851), (1599, 2873), (1602, 2894),
  (1647, 2963), (1685, 2983), (1691, 2987), (1696, 2997), (1766, 3026),
  (1777, 3030), (1783, 3043), (1794, 3052), (1795, 3056), (1894, 3114),
  (1895, 3118), (1900, 3122), (1983, 3179), (1992, 3186), (1993, 3189),
  (1998, 3195), (1999, 3202), (2004, 3218)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0Y1_check. -/
theorem Z1Split55A0X0Y1_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split55A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0Y1_pairs. -/
theorem Z1Split55A0X0Y1_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks0S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks0S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split55A0X0Y1Certs
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
  · exact Z1Split55A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0X0_pairs. -/
theorem Z1Split55A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split55A0X0Y0_pairs x hx y hy hw
  · exact Z1Split55A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split55A0_pairs. -/
theorem Z1Split55A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split55A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split55_check. -/
theorem Z1Split55_check : checkSplit m4TZ1 (0, 5, 3, 0) = true := by
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
    · exact Z1Split55A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split56A0X0Y0Certs : List (Nat × Nat) := [
  (14, 84), (35, 176), (46, 225), (54, 254), (55, 277),
  (57, 284), (94, 447), (104, 508), (124, 602), (135, 663),
  (136, 686), (138, 689), (142, 702), (164, 817), (197, 1024),
  (209, 1139), (215, 1181), (240, 1333), (252, 1434), (255, 1468),
  (259, 1478), (265, 1508), (284, 1660), (313, 1886), (324, 2054),
  (326, 2094), (340, 2166), (357, 2369), (363, 2392), (369, 2447),
  (381, 2589), (397, 2695), (406, 2946), (418, 2995), (424, 3041)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0X0Y0_check. -/
theorem Z1Split56A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split56A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0X0Y0_pairs. -/
theorem Z1Split56A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 6
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split56A0X0Y0Certs
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
  · exact Z1Split56A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0X0_pairs. -/
theorem Z1Split56A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split56A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split56A0_pairs. -/
theorem Z1Split56A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split56A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split56_check. -/
theorem Z1Split56_check : checkSplit m4TZ1 (0, 6, 2, 0) = true := by
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
    · exact Z1Split56A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split57A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0X0Y0_check. -/
theorem Z1Split57A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split57A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0X0Y0_pairs. -/
theorem Z1Split57A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 7
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split57A0X0Y0Certs
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
  · exact Z1Split57A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0X0_pairs. -/
theorem Z1Split57A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split57A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split57A0_pairs. -/
theorem Z1Split57A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split57A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split57_check. -/
theorem Z1Split57_check : checkSplit m4TZ1 (0, 7, 1, 0) = true := by
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
    · exact Z1Split57A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split58A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0X0Y0_check. -/
theorem Z1Split58A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split58A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0X0Y0_pairs. -/
theorem Z1Split58A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 8 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 8
    outerMasks0S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split58A0X0Y0Certs
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
  · exact Z1Split58A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0X0_pairs. -/
theorem Z1Split58A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 8 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split58A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split58A0_pairs. -/
theorem Z1Split58A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 8 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split58A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split58_check. -/
theorem Z1Split58_check : checkSplit m4TZ1 (0, 8, 0, 0) = true := by
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
    · exact Z1Split58A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split59A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0X0Y0_check. -/
theorem Z1Split59A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split59A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0X0Y0_pairs. -/
theorem Z1Split59A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split59A0X0Y0Certs
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
  · exact Z1Split59A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0X0_pairs. -/
theorem Z1Split59A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split59A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split59A0_pairs. -/
theorem Z1Split59A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 7 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split59A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split59_check. -/
theorem Z1Split59_check : checkSplit m4TZ1 (1, 0, 7, 3) = true := by
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
    · exact Z1Split59A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split60A0X0Y0Certs : List (Nat × Nat) := [
  (10, 1281), (57, 2276), (76, 1761), (102, 3246), (149, 2467),
  (202, 1955), (228, 3019), (281, 3085), (344, 1708), (386, 2817),
  (390, 1138), (467, 2019), (530, 1255), (545, 2790), (572, 2053),
  (653, 2883), (715, 1387), (726, 2928), (838, 2262), (878, 2292)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0X0Y0_check. -/
theorem Z1Split60A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split60A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0X0Y0_pairs. -/
theorem Z1Split60A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split60A0X0Y0Certs
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
  · exact Z1Split60A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0X0_pairs. -/
theorem Z1Split60A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split60A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split60A0_pairs. -/
theorem Z1Split60A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split60A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split60_check. -/
theorem Z1Split60_check : checkSplit m4TZ1 (1, 1, 6, 3) = true := by
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
    · exact Z1Split60A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split61A0X0Y0Certs : List (Nat × Nat) := [
  (99, 1277), (106, 576), (115, 1799), (119, 1807), (180, 2825),
  (279, 517), (297, 2044), (298, 2813), (524, 1788), (573, 2143),
  (588, 2202), (605, 3168), (700, 2572), (746, 1928), (788, 3165),
  (874, 2902), (894, 1150), (1074, 1705), (1084, 1283), (1096, 1785),
  (1100, 2028), (1161, 2903), (1198, 2768), (1341, 1794), (1443, 2774),
  (1453, 2693), (1536, 1326), (1662, 2917), (1713, 2920), (1722, 3237),
  (1741, 491), (1928, 1620), (1993, 856), (1999, 761), (2109, 3065),
  (2135, 2775), (2152, 502), (2459, 3145), (2635, 2716), (2636, 2320),
  (2647, 1793), (2695, 2070), (2823, 2733), (2842, 1325), (2911, 2898),
  (2930, 1219), (3106, 3017), (3152, 1704), (3192, 760), (3304, 2411),
  (3316, 1529), (3372, 2152), (3463, 3066), (3695, 1266), (3932, 1113),
  (3992, 1134), (4176, 2476), (4214, 2546), (4268, 1131), (4278, 1613),
  (4321, 1114), (4444, 759), (4835, 1710), (4903, 2330), (4959, 938),
  (4966, 1806), (4970, 1801), (4996, 427), (5082, 2074), (5106, 2265),
  (5242, 1072), (5307, 1902), (5308, 2769), (5329, 1703), (5404, 2828),
  (5549, 2151), (5602, 2645), (5623, 956), (5675, 971), (5803, 1125),
  (5819, 1124), (5871, 1213), (5925, 1612), (6006, 2486), (6018, 3086),
  (6136, 716), (6582, 2022), (6597, 2020), (6695, 2052), (6879, 3010),
  (6890, 3148), (6937, 2049), (6949, 2564), (7157, 1611), (7399, 2878),
  (7402, 990), (7525, 1275), (7624, 2885), (7678, 1752), (7687, 2014),
  (7691, 1804), (7774, 2319), (7871, 968), (7874, 974), (7912, 1962),
  (8016, 2724), (8017, 2326), (8049, 1200), (8125, 2620), (8216, 1782),
  (8332, 850), (8341, 1802), (8401, 2037), (8536, 2038), (8639, 2567),
  (8673, 3160), (8689, 2031), (8824, 1538), (9190, 3245), (9212, 2925),
  (9277, 2890), (9300, 2884), (9388, 2924), (9548, 961), (9561, 1293),
  (9883, 2566), (10030, 2186), (10037, 2767), (10045, 1827), (10086, 1781),
  (10239, 2876), (10252, 1685), (10282, 2282), (10308, 1860), (10495, 2905),
  (10501, 2900), (10597, 964), (10609, 1715), (10695, 2912), (10791, 2913),
  (10873, 3249), (11115, 2497), (11707, 3248), (11754, 658), (11832, 1371),
  (11845, 2318), (11859, 2269), (11923, 1274), (12077, 2153), (12092, 965),
  (12130, 2644), (12520, 3172), (12658, 1428), (12698, 973), (12701, 970),
  (12801, 2231), (12820, 2763), (12840, 2117), (12904, 1683), (12945, 1795)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0X0Y0_check. -/
theorem Z1Split61A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split61A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0X0Y0_pairs. -/
theorem Z1Split61A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split61A0X0Y0Certs
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
  · exact Z1Split61A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0X0_pairs. -/
theorem Z1Split61A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split61A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split61A0_pairs. -/
theorem Z1Split61A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split61A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split61_check. -/
theorem Z1Split61_check : checkSplit m4TZ1 (1, 2, 5, 3) = true := by
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
    · exact Z1Split61A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split62A0X0Y0Certs : List (Nat × Nat) := [
  (67, 1658), (1006, 2643), (1051, 2766), (1068, 498), (1275, 1786),
  (1327, 979), (1449, 1656), (1766, 2241), (4461, 423), (4612, 1720),
  (5569, 412), (5602, 2747), (8013, 2617), (8377, 2410), (8809, 1521),
  (13413, 986), (13513, 1751), (13709, 1415), (14236, 410), (17542, 2490),
  (19180, 3084), (20088, 2477), (22333, 1194), (22762, 2317), (22769, 518),
  (22800, 2130), (23539, 1079), (23591, 1808), (24358, 409), (24370, 1995),
  (24449, 2259), (24765, 1763), (24958, 1087), (25459, 1227), (25642, 1292),
  (26727, 962), (28602, 3003), (32284, 2018), (34824, 472), (35552, 1291),
  (35856, 2755), (35868, 1151), (35916, 561), (36058, 2289), (36740, 1924),
  (36850, 959), (36884, 2852), (36931, 1742), (37107, 2256), (37511, 2704),
  (37844, 1969), (38192, 1981), (39728, 1789), (41420, 861), (47825, 1081),
  (48054, 2209), (48116, 954), (48213, 2075), (49333, 2896), (52176, 1394),
  (54718, 1996), (54730, 416), (55098, 2819), (55219, 1675), (55626, 1285),
  (55967, 983), (58789, 1420), (59114, 2853), (59148, 975), (59748, 1237),
  (59778, 2175), (60021, 2815), (60285, 644)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0Y0_check. -/
theorem Z1Split62A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split62A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0Y0_pairs. -/
theorem Z1Split62A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split62A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk0_bound
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
      exact Z1M3Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z1Split62A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split62A0X0Y1Certs : List (Nat × Nat) := [
  (220, 1749), (697, 2810), (1455, 1907), (3624, 2687), (3683, 2273),
  (4181, 937), (4252, 2306), (4276, 1127), (4527, 2736), (4600, 1437),
  (4646, 1816), (4880, 629), (7685, 2114), (10441, 1831), (12324, 2671),
  (12499, 966), (12685, 2042), (12806, 1384), (12846, 2161), (13758, 1242),
  (13794, 2113), (13796, 2226), (15406, 505), (21355, 2466), (22577, 1189),
  (22620, 1248), (22968, 2787), (23101, 1405), (23841, 2263), (24954, 1823),
  (25095, 2310), (25724, 1796), (25991, 2874), (28451, 1137), (31647, 3149),
  (34403, 3083), (34735, 405), (34923, 2302), (35140, 1973), (35186, 2058),
  (36167, 1068), (37022, 1035), (37986, 2125), (38246, 2287), (40375, 2027),
  (43658, 2882), (44708, 1884), (45157, 1894), (46907, 1247), (47129, 1913),
  (47624, 1745), (48115, 1957), (48184, 2646), (48406, 2722), (48408, 2606),
  (49389, 1314), (54376, 2708), (54979, 1721), (55498, 1975), (55633, 1779),
  (55783, 2897), (56311, 2750), (57691, 2275), (59087, 1811), (59610, 1820),
  (59661, 2621), (60645, 2734)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0Y1_check. -/
theorem Z1Split62A0X0Y1_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M3LeftColumns Z1M3RightColumns) Z1Split62A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0Y1_pairs. -/
theorem Z1Split62A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M3LeftColumns Z1M3RightColumns) Z1Split62A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks3S2048Chunk1_bound
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
      exact Z1M3Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z1Split62A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0X0_pairs. -/
theorem Z1Split62A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split62A0X0Y0_pairs x hx y hy hw
  · exact Z1Split62A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split62A0_pairs. -/
theorem Z1Split62A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split62A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split62_check. -/
theorem Z1Split62_check : checkSplit m4TZ1 (1, 3, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split62A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split63A0X0Y0Certs : List (Nat × Nat) := [
  (119, 215), (146, 244), (451, 515), (654, 652), (1000, 909),
  (1252, 1077), (1588, 1343), (1644, 1370), (1765, 1441), (2739, 712),
  (4607, 584), (4696, 646), (5061, 917), (5238, 1043), (5374, 1148),
  (5682, 1364), (5785, 1414), (6090, 87), (9971, 1531), (12161, 86),
  (12549, 473), (13332, 1041), (13365, 1057), (13683, 1300), (13767, 1355),
  (13871, 1407), (14330, 257), (17534, 1182), (22105, 1525), (22564, 381),
  (22604, 425), (22660, 463), (22730, 543), (23357, 977), (23450, 1040),
  (23789, 1289), (24448, 256), (25527, 1067), (25543, 1083), (25746, 1253),
  (25811, 1288), (26989, 666), (28472, 239), (34946, 575), (35067, 656),
  (35431, 921), (35512, 988), (35648, 1069), (35787, 1204), (35791, 1207),
  (36034, 1358), (36513, 181), (36835, 470), (37027, 618), (37106, 665),
  (37700, 1105), (38064, 1363), (40224, 1442), (41110, 639), (46632, 180),
  (46891, 424), (47149, 621), (47204, 651), (48063, 1278), (48125, 1332),
  (48296, 1422), (48310, 1440), (52302, 1399), (55097, 513), (55258, 628),
  (55751, 987), (56004, 1191), (56232, 1338), (56297, 1375), (56382, 1412),
  (56401, 1436), (58745, 145), (59028, 418), (59850, 1021), (59961, 1100),
  (60020, 1146), (60122, 1228), (60224, 1290), (60245, 1317), (60366, 1383)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0Y0_check. -/
theorem Z1Split63A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split63A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0Y0_pairs. -/
theorem Z1Split63A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split63A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S256Chunk0 masks3S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S2048Chunk0_bound y hy)
  · exact Z1Split63A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split63A0X0Y1Certs : List (Nat × Nat) := [
  (128, 1717), (521, 2007), (672, 2160), (755, 2206), (770, 2218),
  (1334, 2642), (1484, 2743), (1572, 2818), (4168, 1689), (4170, 1691),
  (4389, 1872), (4571, 1971), (4680, 2122), (4775, 2183), (4857, 2230),
  (4859, 2234), (5632, 2801), (5669, 2867), (10324, 1727), (12335, 1711),
  (12525, 1868), (12622, 1919), (12773, 2059), (12789, 2068), (12989, 2219),
  (13105, 2309), (13567, 2654), (13583, 2667), (13640, 2696), (19434, 2488),
  (22726, 1881), (22764, 1897), (22913, 1999), (22967, 2066), (23015, 2131),
  (23219, 2258), (23275, 2300), (23701, 2632), (23758, 2662), (23775, 2677),
  (24464, 1662), (24791, 1889), (24835, 1915), (24886, 1940), (24985, 2057),
  (25189, 2208), (25306, 2293), (25688, 2591), (25732, 2631), (25785, 2658),
  (25860, 2697), (25931, 2759), (32494, 3162), (33674, 2481), (34852, 1814),
  (34934, 1877), (35012, 1912), (35424, 2248), (35890, 2607), (35999, 2681),
  (36058, 2712), (36143, 2782), (36205, 2857), (36701, 1676), (36773, 1716),
  (36946, 1859), (37128, 1956), (37150, 1977), (37237, 2106), (37463, 2250),
  (37909, 2594), (38081, 2701), (38144, 2754), (38189, 2786), (44066, 2636),
  (46735, 3155), (46963, 1722), (47080, 1825), (47148, 1874), (47309, 1958),
  (47454, 2136), (47512, 2169), (47589, 2212), (48204, 2674), (48320, 2749),
  (49440, 2095), (54370, 2702), (55093, 1714), (55167, 1756), (55552, 2098),
  (55640, 2158), (55649, 2163), (55661, 2172), (55868, 2322), (56343, 2670),
  (56545, 2820), (57689, 2168), (59295, 1824), (59368, 1878), (59642, 2111),
  (59739, 2177), (59839, 2240), (59929, 2305), (60325, 2610), (60601, 2799)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0Y1_check. -/
theorem Z1Split63A0X0Y1_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split63A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0Y1_pairs. -/
theorem Z1Split63A0X0Y1_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks3S2048Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks1S256Chunk0 masks3S2048Chunk1
    (gridWords outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split63A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks3S2048Chunk1_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks1S256Chunk0 masks3S2048Chunk1
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks3S2048Chunk1_bound y hy)
  · exact Z1Split63A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0X0_pairs. -/
theorem Z1Split63A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl
  · exact Z1Split63A0X0Y0_pairs x hx y hy hw
  · exact Z1Split63A0X0Y1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split63A0_pairs. -/
theorem Z1Split63A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split63A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split63_check. -/
theorem Z1Split63_check : checkSplit m4TZ1 (1, 4, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split63A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

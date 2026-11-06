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
def Z1Split64A0X0Y0Certs : List (Nat × Nat) := [
  (85, 387), (180, 914), (181, 918), (204, 1060), (239, 1330),
  (297, 1768), (326, 2092), (387, 2625), (874, 52), (884, 85),
  (983, 550), (1054, 931), (1161, 1700), (1162, 1713), (1190, 1944),
  (1209, 2157), (2635, 135), (2664, 253), (2805, 1020), (2823, 1174),
  (2834, 1223), (2844, 1312), (2905, 1737), (3013, 2795), (4825, 199),
  (4903, 572), (4904, 578), (4915, 623), (5082, 1767), (5090, 1854),
  (5123, 2148), (5166, 2587), (5242, 124), (5307, 397), (5355, 662),
  (5411, 1011), (5499, 1640), (5530, 1876), (5552, 2110), (5606, 2609),
  (7399, 51), (7430, 177), (7509, 555), (7571, 901), (7624, 1271),
  (7625, 1287), (7642, 1376), (7783, 2628), (7854, 132), (7912, 377),
  (7913, 380), (7929, 460), (8016, 945), (8082, 1432), (8134, 1851),
  (8224, 2673), (10030, 136), (10109, 506), (10133, 613), (10230, 1235),
  (10282, 1634), (10291, 1671), (10306, 1844), (10352, 2244), (11754, 65),
  (11832, 398), (11868, 600), (11954, 1140), (11956, 1169), (11990, 1362),
  (12075, 2101), (12127, 2592), (12622, 61), (12658, 207), (12659, 211),
  (12665, 231), (12801, 946), (12853, 1322), (12939, 2055), (12960, 2217)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0X0Y0_check. -/
theorem Z1Split64A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0X0Y0_pairs. -/
theorem Z1Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split64A0X0Y0Certs
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
  · exact Z1Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0X0_pairs. -/
theorem Z1Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split64A0_pairs. -/
theorem Z1Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split64_check. -/
theorem Z1Split64_check : checkSplit m4TZ1 (1, 5, 2, 0) = true := by
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
    · exact Z1Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split65A0X0Y0Certs : List (Nat × Nat) := [
  (47, 676), (92, 31), (143, 1452), (216, 91), (297, 2340),
  (402, 316), (479, 2938), (588, 781), (641, 273), (720, 7)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0X0Y0_check. -/
theorem Z1Split65A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0X0Y0_pairs. -/
theorem Z1Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split65A0X0Y0Certs
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
  · exact Z1Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0X0_pairs. -/
theorem Z1Split65A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split65A0_pairs. -/
theorem Z1Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split65_check. -/
theorem Z1Split65_check : checkSplit m4TZ1 (1, 6, 1, 0) = true := by
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
    · exact Z1Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0X0Y0_check. -/
theorem Z1Split66A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0X0Y0_pairs. -/
theorem Z1Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split66A0X0Y0Certs
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
  · exact Z1Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0X0_pairs. -/
theorem Z1Split66A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split66A0_pairs. -/
theorem Z1Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 7 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split66_check. -/
theorem Z1Split66_check : checkSplit m4TZ1 (1, 7, 0, 0) = true := by
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
    · exact Z1Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split67A0X0Y0Certs : List (Nat × Nat) := [
  (4, 2889), (25, 2443), (33, 3064), (55, 1805), (87, 3138),
  (101, 960), (138, 2011), (186, 2485), (206, 1787), (259, 2870),
  (297, 3159), (322, 1600), (363, 2006), (404, 2553), (424, 2865)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0X0Y0_check. -/
theorem Z1Split67A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0X0Y0_pairs. -/
theorem Z1Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split67A0X0Y0Certs
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
  · exact Z1Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0X0_pairs. -/
theorem Z1Split67A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split67A0_pairs. -/
theorem Z1Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 6 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split67_check. -/
theorem Z1Split67_check : checkSplit m4TZ1 (2, 0, 6, 3) = true := by
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
    · exact Z1Split67A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split68A0X0Y0Certs : List (Nat × Nat) := [
  (54, 2887), (126, 2927), (138, 2862), (143, 3243), (149, 3244),
  (272, 2659), (478, 1657), (513, 2313), (677, 2164), (750, 174),
  (761, 1559), (762, 3185), (777, 846), (1296, 1121), (1393, 2517),
  (1659, 2727), (1663, 2228), (1730, 245), (2000, 1800), (2048, 414),
  (2167, 2720), (2483, 1132), (2612, 504), (2627, 2532), (2628, 3018),
  (2639, 879), (2829, 2409), (3552, 2034), (3739, 3211), (3779, 1210),
  (4096, 468), (4155, 2073), (4159, 2043), (4285, 647), (4431, 2904),
  (4609, 2824), (4675, 1791), (4784, 969), (4930, 2731), (4963, 1961),
  (5427, 2050), (5580, 1133), (5586, 1136), (5591, 1609), (5603, 3233),
  (5925, 3081), (5958, 1655), (6401, 3173), (6457, 1549), (6888, 2908),
  (7103, 2555), (7224, 3098), (7241, 752), (7672, 1075), (7791, 2872),
  (7794, 2892), (7946, 1190), (7978, 1408), (8101, 2753), (8310, 2814),
  (8524, 1486), (8759, 2926), (8912, 2051), (8922, 2024), (8927, 2563),
  (8937, 3234), (9246, 1783), (9411, 1753), (9420, 407), (10077, 3147),
  (10203, 1261), (10247, 1602), (10736, 1965), (10876, 1798), (10891, 1033),
  (10893, 616), (11045, 413), (11078, 2295), (11224, 2190), (11772, 1286),
  (11911, 1726), (11942, 957), (12194, 2281), (12525, 2332), (12545, 2829),
  (12712, 1777), (12724, 1905), (12727, 1368), (12880, 967), (12999, 1430)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0X0Y0_check. -/
theorem Z1Split68A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0X0Y0_pairs. -/
theorem Z1Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split68A0X0Y0Certs
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
  · exact Z1Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0X0_pairs. -/
theorem Z1Split68A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split68A0_pairs. -/
theorem Z1Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split68_check. -/
theorem Z1Split68_check : checkSplit m4TZ1 (2, 1, 5, 3) = true := by
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
    · exact Z1Split68A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split69A0X0Y0Certs : List (Nat × Nat) := [
  (470, 1755), (665, 1696), (682, 2804), (731, 1193), (1795, 2860),
  (6705, 395), (6866, 1917), (6927, 1111), (7016, 2859), (7499, 1871),
  (7696, 1119), (7698, 458), (7742, 2678), (7897, 3183), (11013, 1490),
  (20050, 2565), (20099, 305), (23969, 2668), (24008, 2213), (24111, 1152),
  (24131, 1997), (24177, 2793), (24249, 2327), (25046, 2752), (25105, 2788),
  (25174, 2328), (26876, 2069), (26934, 465), (28732, 2072), (28835, 2009),
  (28913, 2207), (29611, 2016), (29816, 2757), (29871, 944), (30590, 1487),
  (31288, 2986), (31529, 2666), (31650, 1388), (31702, 2030), (31705, 1058),
  (31912, 3005), (33628, 2331), (33693, 426), (38104, 2416), (40926, 749),
  (40975, 2496), (46041, 3087), (50648, 925), (52299, 1565), (54054, 3247),
  (54128, 766), (54802, 1123), (59405, 2242), (59476, 2312), (59488, 2792),
  (60149, 1256), (60211, 1759), (60327, 2076), (60352, 2854), (60356, 2221),
  (60411, 2676), (61802, 2714), (62120, 2188), (62164, 1693), (63959, 1252),
  (64171, 1647), (64237, 1231), (64265, 2255), (64409, 1071), (64616, 2797),
  (66674, 2700), (66685, 2324), (66740, 2789), (66936, 1280), (67507, 2845),
  (67666, 2868), (67744, 1695), (69263, 2880), (69378, 1766), (69500, 2227),
  (70732, 2412), (71291, 729), (71468, 2257), (71540, 2264), (71638, 1942),
  (71819, 2901), (71825, 2266), (71861, 1941), (72099, 1246), (72246, 875),
  (74200, 2891), (74264, 989), (74492, 1564), (79353, 1157), (81273, 3091),
  (85802, 1597), (85879, 3171), (86424, 1109), (87485, 1594), (92647, 2041),
  (93532, 1610), (93938, 2956), (99044, 1730), (101559, 2542), (102922, 2916),
  (104625, 2992), (104699, 1619), (104891, 2036)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X0Y0_check. -/
theorem Z1Split69A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X0Y0_pairs. -/
theorem Z1Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X0_pairs. -/
theorem Z1Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split69A0X1Y0Certs : List (Nat × Nat) := [
  (349, 250), (398, 1826), (789, 1579), (896, 2185), (1215, 1206),
  (1270, 2718), (1308, 2840), (2614, 2839), (2624, 1900), (2645, 1345),
  (2840, 1423), (2902, 1920), (3014, 1107), (4903, 214), (5131, 1118),
  (5183, 1417), (5320, 1880), (5459, 1066), (5603, 1424), (7449, 1357),
  (7627, 243), (7629, 1110), (7798, 2224), (7925, 1960), (8165, 2619),
  (11091, 2541), (13509, 1537), (13642, 830), (17694, 2071), (19564, 2002),
  (24009, 2145), (26316, 2550), (26395, 824), (26538, 2013), (27970, 2547),
  (34250, 3203), (36036, 3016), (38056, 758), (38199, 2492), (38420, 2911),
  (42755, 516), (42829, 2823), (43513, 659), (43808, 2247), (44783, 2454),
  (45328, 1366), (45545, 627), (45573, 1921), (45698, 183), (46457, 829),
  (47424, 2040), (47544, 2664), (47613, 2001), (47875, 182), (47883, 2010),
  (47904, 2719), (47954, 2189), (48084, 2760), (48151, 2323), (50036, 2029),
  (50254, 583), (50333, 2314), (50513, 2325), (50665, 2680), (50799, 1954),
  (52770, 2211), (52964, 645), (52967, 2015), (53021, 1953), (60648, 855),
  (62707, 3146), (62919, 715), (63098, 2875), (64627, 3059), (66689, 2811),
  (66750, 2816), (66876, 1426), (67666, 1149), (67740, 2871), (69217, 1429),
  (69557, 2116), (70559, 3009), (71455, 2291), (71521, 2173), (71544, 2761),
  (71666, 1707), (71871, 2762), (71962, 2223), (72163, 1382), (72294, 522),
  (72975, 746), (73993, 2842), (74196, 1232), (74264, 2858), (74472, 519),
  (74486, 2869), (74520, 1943), (74594, 1425), (74717, 2254), (74767, 2803),
  (76609, 2899), (76837, 1299), (76952, 2723), (78341, 1406), (78383, 2877),
  (78399, 2812), (78552, 1748)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X1Y0_check. -/
theorem Z1Split69A0X1Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X1Y0_pairs. -/
theorem Z1Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split69A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M3Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M3Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M3Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M3Left_eq
    · exact Z1M3Right_eq
    · intro x hx
      exact Z1M3Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0X1_pairs. -/
theorem Z1Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69A0_pairs. -/
theorem Z1Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split69A0X0_pairs x hx y hy hw
  · exact Z1Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split69_check. -/
theorem Z1Split69_check : checkSplit m4TZ1 (2, 2, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split69A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y0Certs : List (Nat × Nat) := [
  (9939, 455), (11441, 171), (11443, 172), (11573, 300), (23024, 353),
  (25189, 260), (25472, 511), (28154, 466), (28350, 240), (30349, 394),
  (30408, 453), (31719, 402), (33083, 401), (35169, 234), (39996, 487),
  (40000, 492), (48674, 509), (67750, 486), (69748, 233), (75731, 303),
  (75733, 304), (99722, 178), (103498, 308)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y0_check. -/
theorem Z1Split70A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y0_pairs. -/
theorem Z1Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y1Certs : List (Nat × Nat) := [
  (365, 538), (518, 630), (8442, 617), (9283, 711), (19904, 564),
  (23848, 547), (24685, 615), (26637, 726), (31733, 757), (44828, 567),
  (50042, 669), (51308, 563), (53970, 640), (61529, 631), (61808, 568),
  (62063, 764), (62067, 765), (63093, 718)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y1_check. -/
theorem Z1Split70A0X0Y1_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y1_pairs. -/
theorem Z1Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y2Certs : List (Nat × Nat) := [
  (5050, 915), (5969, 867), (18071, 941), (30541, 849), (37809, 929),
  (37875, 993), (42255, 862), (47785, 895), (50474, 943), (52104, 951),
  (53722, 950), (56056, 793), (64059, 934), (65441, 997), (73761, 924)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y2_check. -/
theorem Z1Split70A0X0Y2_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y2_pairs. -/
theorem Z1Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y2Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y3Certs : List (Nat × Nat) := [
  (6824, 1025), (7015, 1188), (7208, 1018), (7483, 1225), (23031, 1199),
  (24623, 1195), (29216, 1022), (30913, 1078), (32076, 1053), (55381, 1144),
  (55519, 1254), (57234, 1031), (58895, 1065), (59036, 1203), (59232, 1030),
  (59304, 1073), (59489, 1229), (62054, 1046), (62272, 1217), (63725, 1101),
  (63829, 1198), (68044, 1037), (68751, 1265), (74526, 1102), (74532, 1115),
  (85777, 1142), (93447, 1209), (96341, 1262)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y3_check. -/
theorem Z1Split70A0X0Y3_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y3_pairs. -/
theorem Z1Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y3Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y4Certs : List (Nat × Nat) := [
  (3234, 1526), (4228, 1536), (7293, 1331), (8361, 1385), (8423, 1413),
  (8943, 1464), (28840, 1497), (29705, 1404), (34665, 1512), (35569, 1473),
  (37395, 1381), (40759, 1369), (42440, 1527), (45632, 1393), (56548, 1593),
  (56564, 1604), (66990, 1416), (68186, 1607), (71658, 1327), (74105, 1344),
  (77056, 1367), (80720, 1552), (90461, 1608), (110412, 1349), (116465, 1518),
  (119758, 1435)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y4_check. -/
theorem Z1Split70A0X0Y4_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y4_pairs. -/
theorem Z1Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y4Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y5Certs : List (Nat × Nat) := [
  (370, 1688), (4346, 1764), (18877, 1702), (21750, 1773), (37622, 1684),
  (38291, 1760), (42407, 1746), (42447, 1772), (47156, 1812), (62817, 1735),
  (62911, 1830)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y5_check. -/
theorem Z1Split70A0X0Y5_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y5_pairs. -/
theorem Z1Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y5Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y6Certs : List (Nat × Nat) := [
  (4635, 1925), (11388, 2062), (13857, 1883), (18509, 1964), (20041, 2000),
  (20634, 1991), (21685, 1890), (21942, 1873), (23344, 2004), (41525, 1914),
  (46715, 1968), (49492, 2064), (49870, 1885), (51224, 1972), (53269, 1935)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y6_check. -/
theorem Z1Split70A0X0Y6_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y6_pairs. -/
theorem Z1Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y6Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y7Certs : List (Nat × Nat) := [
  (146, 2196), (459, 2187), (18075, 2222), (18350, 2198), (18826, 2299),
  (19948, 2180), (21655, 2225), (22201, 2162), (23650, 2260), (23710, 2307),
  (25212, 2215), (25277, 2267), (48392, 2285), (50730, 2121), (51704, 2120),
  (53906, 2280), (55261, 2104), (55494, 2253), (59683, 2229), (64280, 2272)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y7_check. -/
theorem Z1Split70A0X0Y7_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y7_pairs. -/
theorem Z1Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y7Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y8Certs : List (Nat × Nat) := [
  (6385, 2394), (6472, 2449), (13542, 2482), (14983, 2495), (22761, 2552),
  (25631, 2363), (28683, 2499), (34853, 2417), (40887, 2475), (51029, 2425),
  (57375, 2455), (58304, 2378), (60289, 2523), (65492, 2483), (75472, 2362),
  (79953, 2543), (79959, 2545)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y8_check. -/
theorem Z1Split70A0X0Y8_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y8_pairs. -/
theorem Z1Split70A0X0Y8_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y8Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk8
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk8_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z1Split70A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y9Certs : List (Nat × Nat) := [
  (1181, 2630), (1837, 2838), (1848, 2849), (1855, 2861), (5716, 2629),
  (20924, 2679), (22017, 2650), (23150, 2649), (23171, 2663), (25956, 2770),
  (29201, 2652), (41358, 2690), (47014, 2686), (51642, 2745), (53690, 2598),
  (55766, 2717), (56268, 2827), (58356, 2688), (58931, 2856), (60434, 2844),
  (62170, 2698), (62495, 2675), (62554, 2703), (62865, 2669), (64604, 2863),
  (64800, 2692), (84227, 2805)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y9_check. -/
theorem Z1Split70A0X0Y9_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y9_pairs. -/
theorem Z1Split70A0X0Y9_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y9Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk9
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk9_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z1Split70A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X0Y10Certs : List (Nat × Nat) := [
  (2028, 3242), (7364, 2984), (18716, 2974), (29644, 2955), (29795, 3046),
  (45386, 3156), (47377, 3144), (47434, 3169), (47843, 3170), (48825, 3020),
  (61310, 2951), (67438, 2975), (69537, 3021), (72594, 3163), (83033, 3092),
  (87480, 3082), (92440, 3142)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y10_check. -/
theorem Z1Split70A0X0Y10_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0Y10_pairs. -/
theorem Z1Split70A0X0Y10_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X0Y10Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk0 masks3S512Chunk10
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk10_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z1Split70A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X0_pairs. -/
theorem Z1Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z1Split70A0X0Y0_pairs x hx y hy hw
  · exact Z1Split70A0X0Y1_pairs x hx y hy hw
  · exact Z1Split70A0X0Y2_pairs x hx y hy hw
  · exact Z1Split70A0X0Y3_pairs x hx y hy hw
  · exact Z1Split70A0X0Y4_pairs x hx y hy hw
  · exact Z1Split70A0X0Y5_pairs x hx y hy hw
  · exact Z1Split70A0X0Y6_pairs x hx y hy hw
  · exact Z1Split70A0X0Y7_pairs x hx y hy hw
  · exact Z1Split70A0X0Y8_pairs x hx y hy hw
  · exact Z1Split70A0X0Y9_pairs x hx y hy hw
  · exact Z1Split70A0X0Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y0Certs : List (Nat × Nat) := [
  (134, 235), (638, 294), (5624, 259), (9745, 296), (11739, 445),
  (13236, 137), (14349, 348), (16559, 288), (35069, 113), (44989, 467),
  (45912, 488), (46446, 128), (46602, 298), (47767, 510), (49712, 213),
  (49750, 251), (55380, 403), (74013, 385), (74051, 430), (75013, 462),
  (77900, 204), (78122, 392)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y0_check. -/
theorem Z1Split70A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y0_pairs. -/
theorem Z1Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y1Certs : List (Nat × Nat) := [
  (713, 769), (4052, 573), (6249, 603), (9053, 552), (28399, 704),
  (36051, 750), (36231, 612), (36259, 632), (37120, 738), (42100, 668),
  (56143, 643), (57552, 626), (58785, 745), (58797, 754), (61471, 582),
  (61579, 660)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y1_check. -/
theorem Z1Split70A0X1Y1_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y1_pairs. -/
theorem Z1Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y2Certs : List (Nat × Nat) := [
  (327, 792), (895, 940), (10175, 860), (32030, 978), (33110, 828),
  (35478, 898), (58585, 952)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y2_check. -/
theorem Z1Split70A0X1Y2_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y2_pairs. -/
theorem Z1Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y2Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y3Certs : List (Nat × Nat) := [
  (4796, 1297), (5114, 1250), (7292, 1062), (7324, 1099), (10267, 1214),
  (10360, 1267), (46026, 1027), (46368, 1273), (62104, 1074), (63727, 1103),
  (65900, 1238), (66181, 1143), (70528, 1106)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y3_check. -/
theorem Z1Split70A0X1Y3_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y3_pairs. -/
theorem Z1Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y3Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y4Certs : List (Nat × Nat) := [
  (135, 1390), (3010, 1374), (3134, 1444), (5533, 1431), (8725, 1320),
  (9365, 1401), (12547, 1617), (12553, 1618), (14886, 1540), (42550, 1616),
  (49722, 1535), (49843, 1624), (56181, 1335), (58604, 1336), (64638, 1491),
  (71868, 1472), (74282, 1445), (76405, 1599), (77044, 1360), (77091, 1389),
  (78805, 1584), (82860, 1365), (84279, 1350)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y4_check. -/
theorem Z1Split70A0X1Y4_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y4_pairs. -/
theorem Z1Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y4Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y5Certs : List (Nat × Nat) := [
  (33, 1663), (422, 1728), (4717, 1654), (16733, 1741), (17800, 1725),
  (27650, 1674), (28901, 1757), (39762, 1650), (43021, 1815), (45487, 1774),
  (46963, 1667), (47159, 1813), (48655, 1681)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y5_check. -/
theorem Z1Split70A0X1Y5_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y5_pairs. -/
theorem Z1Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y5Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y6Certs : List (Nat × Nat) := [
  (119, 1909), (1974, 1939), (2092, 2063), (3333, 1867), (4003, 1903),
  (5228, 1916), (5299, 1951), (5500, 1901), (5609, 1963), (12310, 1855),
  (13443, 2003), (13449, 2023), (20387, 2061), (29594, 1948), (29640, 1998),
  (30032, 1865), (32945, 2008), (34732, 1990), (46718, 1970), (47729, 1864),
  (49296, 1899), (49581, 1888), (51353, 1879), (52888, 1893), (53128, 1863)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y6_check. -/
theorem Z1Split70A0X1Y6_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y6_pairs. -/
theorem Z1Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y6Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y7Certs : List (Nat × Nat) := [
  (48, 2135), (176, 2205), (685, 2126), (2264, 2311), (3669, 2159),
  (5938, 2154), (30552, 2096), (31902, 2137), (32752, 2268), (35878, 2184),
  (35964, 2237), (36051, 2298), (37699, 2333), (38986, 2308), (39881, 2245),
  (49834, 2170), (50712, 2105), (51686, 2103), (55610, 2127), (58614, 2174),
  (58698, 2220)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y7_check. -/
theorem Z1Split70A0X1Y7_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y7_pairs. -/
theorem Z1Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y7Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y8Certs : List (Nat × Nat) := [
  (420, 2396), (3469, 2560), (15766, 2562), (21080, 2371), (30704, 2465),
  (37233, 2374), (57100, 2494), (57206, 2574)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y8_check. -/
theorem Z1Split70A0X1Y8_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y8_pairs. -/
theorem Z1Split70A0X1Y8_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y8Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk8
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk8_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z1Split70A0X1Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y9Certs : List (Nat × Nat) := [
  (191, 2711), (2509, 2751), (6835, 2611), (13461, 2742), (37249, 2721),
  (37368, 2826), (38030, 2738), (41389, 2707), (41775, 2713), (41814, 2744),
  (41863, 2784), (43571, 2657), (44434, 2725), (45983, 2756), (46053, 2808),
  (56839, 2684), (58353, 2685), (58621, 2612), (58899, 2802), (58930, 2855),
  (60202, 2655), (64605, 2866), (64652, 2599), (66541, 2597), (66857, 2841),
  (68258, 2730)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y9_check. -/
theorem Z1Split70A0X1Y9_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y9_pairs. -/
theorem Z1Split70A0X1Y9_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y9Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk9
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk9_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z1Split70A0X1Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split70A0X1Y10Certs : List (Nat × Nat) := [
  (411, 2952), (475, 2999), (6341, 3104), (10522, 3217), (18186, 3157),
  (41572, 3050), (46272, 3240), (58540, 3002), (67892, 3011)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y10_check. -/
theorem Z1Split70A0X1Y10_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1Y10_pairs. -/
theorem Z1Split70A0X1Y10_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z1M0LeftColumns Z1M0RightColumns) Z1Split70A0X1Y10Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks2S256Chunk1 masks3S512Chunk10
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk10_bound
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
      exact Z1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z1Split70A0X1Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0X1_pairs. -/
theorem Z1Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z1Split70A0X1Y0_pairs x hx y hy hw
  · exact Z1Split70A0X1Y1_pairs x hx y hy hw
  · exact Z1Split70A0X1Y2_pairs x hx y hy hw
  · exact Z1Split70A0X1Y3_pairs x hx y hy hw
  · exact Z1Split70A0X1Y4_pairs x hx y hy hw
  · exact Z1Split70A0X1Y5_pairs x hx y hy hw
  · exact Z1Split70A0X1Y6_pairs x hx y hy hw
  · exact Z1Split70A0X1Y7_pairs x hx y hy hw
  · exact Z1Split70A0X1Y8_pairs x hx y hy hw
  · exact Z1Split70A0X1Y9_pairs x hx y hy hw
  · exact Z1Split70A0X1Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70A0_pairs. -/
theorem Z1Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split70A0X0_pairs x hx y hy hw
  · exact Z1Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split70_check. -/
theorem Z1Split70_check : checkSplit m4TZ1 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split71A0X0Y0Certs : List (Nat × Nat) := [
  (483, 227), (536, 483), (633, 1029), (681, 1372), (2144, 2834),
  (2872, 1493), (6804, 1638), (7522, 609), (7601, 1095), (7709, 1896),
  (7741, 2233), (7846, 104), (10908, 170), (11376, 325), (14282, 2382),
  (16896, 2419), (20441, 3152), (24026, 481), (25199, 2833), (26764, 1270),
  (26934, 2728), (27054, 383), (28894, 933), (29604, 130), (31025, 695),
  (31331, 78), (31564, 1354), (31642, 1983), (31718, 2710), (31825, 335),
  (33577, 376), (33628, 641), (37946, 484), (38435, 789), (41139, 1397),
  (43923, 3024), (48712, 3094), (50642, 922), (52566, 2420), (54329, 2633),
  (59564, 2836), (60236, 1093), (61803, 169), (64037, 444), (64046, 482),
  (64070, 605), (64264, 1937), (64409, 155), (64657, 1636), (64998, 927),
  (66588, 167), (66684, 620), (66836, 1646), (66947, 2647), (67130, 694),
  (67720, 1739), (69250, 388), (71167, 1494), (71662, 1988), (71824, 229),
  (72083, 1861), (72119, 2204), (72179, 2831), (72372, 810), (74130, 913),
  (74200, 1402), (74490, 531), (81116, 1089), (81360, 102), (86020, 2090),
  (87618, 928), (89439, 1499), (93896, 2480), (96626, 280), (99038, 1724),
  (101782, 3095), (104544, 708)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X0Y0_check. -/
theorem Z1Split71A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X0Y0_pairs. -/
theorem Z1Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X0Y0Certs
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
  · exact Z1Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X0_pairs. -/
theorem Z1Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split71A0X1Y0Certs : List (Nat × Nat) := [
  (291, 1698), (349, 2278), (691, 1471), (903, 168), (2932, 1989),
  (4996, 1166), (5321, 478), (7589, 1016), (7601, 1094), (7636, 1340),
  (7797, 2779), (7839, 67), (7925, 448), (8559, 1732), (11087, 1170),
  (13617, 638), (19462, 1985), (19643, 328), (26112, 80), (28134, 1731),
  (29948, 2427), (32784, 799), (33986, 278), (38112, 1524), (42673, 206),
  (42829, 1034), (43513, 82), (43713, 1175), (44728, 2372), (45341, 480),
  (46133, 127), (47529, 557), (48254, 2837), (50032, 60), (50666, 1090),
  (52666, 157), (52944, 1869), (52957, 1982), (52976, 2179), (53073, 48),
  (55239, 3107), (62691, 238), (64383, 47), (66877, 1986), (67543, 571),
  (67740, 1906), (67883, 126), (69187, 123), (69217, 241), (70889, 3007),
  (71373, 166), (71543, 1056), (71558, 1192), (71675, 2133), (71981, 1092),
  (72729, 384), (74175, 1236), (74418, 163), (76600, 200), (78398, 457),
  (78536, 1319), (78693, 2661), (78704, 2830)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X1Y0_check. -/
theorem Z1Split71A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X1Y0_pairs. -/
theorem Z1Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split71A0X1Y0Certs
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
  · exact Z1Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0X1_pairs. -/
theorem Z1Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71A0_pairs. -/
theorem Z1Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split71A0X0_pairs x hx y hy hw
  · exact Z1Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split71_check. -/
theorem Z1Split71_check : checkSplit m4TZ1 (2, 4, 2, 0) = true := by
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
    · exact Z1Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split72A0X0Y0Certs : List (Nat × Nat) := [
  (460, 219), (791, 271), (803, 1457), (960, 8), (966, 97),
  (1512, 314), (1723, 368), (1735, 1839), (1854, 1631), (1855, 1836),
  (2006, 2088), (2056, 586), (2319, 184), (2320, 216), (2657, 679),
  (2667, 2347), (2997, 2344), (3002, 29), (3012, 317), (3918, 778),
  (4089, 190), (4102, 1306), (4279, 883), (4288, 2578), (4443, 46),
  (4468, 2581), (4655, 73), (4792, 1304), (4924, 57), (4936, 589),
  (5115, 524), (5116, 585), (5633, 1450), (5639, 2931), (6149, 2939),
  (6156, 100), (6168, 777), (7410, 11), (7611, 1163), (7612, 1302),
  (7665, 523), (7676, 2084), (7934, 435), (7958, 148), (7974, 1632),
  (8137, 120), (8138, 154), (8951, 264), (8967, 2342), (9611, 267),
  (9630, 10), (9642, 315), (9857, 674), (9869, 2940), (9906, 89),
  (10412, 30), (10543, 363), (10544, 436), (10591, 20), (10616, 2085),
  (10715, 71), (10731, 1162), (10888, 2582), (11060, 1000), (11073, 45),
  (11084, 438), (11372, 33), (11388, 776), (11603, 1451), (12107, 675),
  (12187, 119), (12200, 1005), (12259, 882), (12260, 999), (12364, 58),
  (12365, 74), (12541, 17), (12550, 217), (12698, 152), (12895, 1838)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0X0Y0_check. -/
theorem Z1Split72A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0X0Y0_pairs. -/
theorem Z1Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split72A0X0Y0Certs
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
  · exact Z1Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0X0_pairs. -/
theorem Z1Split72A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split72A0_pairs. -/
theorem Z1Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split72_check. -/
theorem Z1Split72_check : checkSplit m4TZ1 (2, 5, 1, 0) = true := by
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
    · exact Z1Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0X0Y0_check. -/
theorem Z1Split73A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0X0Y0_pairs. -/
theorem Z1Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split73A0X0Y0Certs
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
  · exact Z1Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0X0_pairs. -/
theorem Z1Split73A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split73A0_pairs. -/
theorem Z1Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 6 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact Z1Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split73_check. -/
theorem Z1Split73_check : checkSplit m4TZ1 (2, 6, 0, 0) = true := by
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
    · exact Z1Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split74A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X0Y0_check. -/
theorem Z1Split74A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X0Y0_pairs. -/
theorem Z1Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split74A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z1M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X0_pairs. -/
theorem Z1Split74A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split74A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X1Y0_check. -/
theorem Z1Split74A0X1Y0_check : checkGrid m4TZ1 censusZ1 3 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split74A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X1Y0_pairs. -/
theorem Z1Split74A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split74A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z1M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks0S512Chunk0_bound y hy)
  · exact Z1Split74A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0X1_pairs. -/
theorem Z1Split74A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split74A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74A0_pairs. -/
theorem Z1Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 5 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split74A0X0_pairs x hx y hy hw
  · exact Z1Split74A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split74_check. -/
theorem Z1Split74_check : checkSplit m4TZ1 (3, 0, 5, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split74A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split75A0X0Y0Certs : List (Nat × Nat) := [
  (1271, 2571), (1278, 2201), (1283, 3167), (1320, 2918), (1326, 2921),
  (1349, 3241), (9484, 2400), (9780, 346), (9797, 3049), (9807, 825),
  (9872, 3135), (9881, 2513), (9882, 3029), (11389, 2683), (11470, 2402),
  (15438, 1263), (19788, 1743), (21637, 2516), (25393, 1934), (26937, 2554),
  (29627, 751), (29729, 3143), (31989, 3063), (32492, 840), (32513, 361),
  (32519, 717), (32616, 2413), (32627, 3201), (32628, 1530), (35729, 1240),
  (36264, 1489), (36406, 3068), (40032, 1352), (40037, 2498), (40049, 1622),
  (43670, 1026), (43672, 2239), (44138, 1551), (44250, 139), (47438, 1778),
  (47440, 2017), (47605, 1892), (47606, 490), (49091, 3038), (52146, 1244),
  (52320, 1666), (54524, 2522), (55095, 2197), (56312, 406), (56593, 3210)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X0Y0_check. -/
theorem Z1Split75A0X0Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X0Y0_pairs. -/
theorem Z1Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split75A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z1M3Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X0_pairs. -/
theorem Z1Split75A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split75A0X1Y0Certs : List (Nat × Nat) := [
  (122, 3161), (138, 2045), (147, 2561), (905, 1484), (2213, 1601),
  (2411, 297), (5956, 611), (5965, 2785), (6075, 858), (6756, 859),
  (6761, 1539), (6777, 880), (6870, 2487), (6882, 3088), (6893, 3141),
  (9870, 811), (10865, 1792), (10874, 2032), (11122, 1359), (11128, 495),
  (12053, 2551), (12191, 1218), (12981, 1259), (13053, 2415), (13282, 1400),
  (19053, 1548), (20187, 1706), (20744, 1226), (20746, 2881), (20788, 2689),
  (21005, 1112), (21028, 2706), (21149, 2389), (23297, 1598), (24473, 1747),
  (26712, 1264), (26882, 560), (30770, 3216), (31611, 1550), (33456, 955),
  (33829, 3080), (37114, 3212), (38191, 1482), (39162, 1279), (39547, 3090),
  (41582, 559), (42716, 2194), (43120, 1673), (43130, 2906), (43428, 337),
  (43478, 1120), (43496, 2214), (44817, 3150), (44987, 935), (46716, 1245),
  (50022, 1780), (53139, 3102), (55884, 1729), (56125, 3154), (57151, 2518)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X1Y0_check. -/
theorem Z1Split75A0X1Y0_check : checkGrid m4TZ1 censusZ1 3 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split75A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X1Y0_pairs. -/
theorem Z1Split75A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 3 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns) Z1Split75A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 3 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M3LeftColumns Z1M3RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z1M3Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z1M3Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split75A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0X1_pairs. -/
theorem Z1Split75A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split75A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75A0_pairs. -/
theorem Z1Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 3 x y 0) = 4 →
      sweepAccept m4TZ1 3 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split75A0X0_pairs x hx y hy hw
  · exact Z1Split75A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split75_check. -/
theorem Z1Split75_check : checkSplit m4TZ1 (3, 1, 4, 3) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M3Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M3Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M3_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split75A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y0Certs : List (Nat × Nat) := [
  (4872, 399), (11895, 161), (14606, 142), (15549, 179), (19224, 212),
  (22135, 379), (25692, 307), (27927, 287), (28398, 295), (29015, 432),
  (35088, 146), (40447, 474), (41966, 209), (45835, 419), (46831, 499),
  (47313, 512), (52481, 255), (54992, 461), (56562, 242), (71783, 431),
  (77709, 434), (82990, 292), (84628, 521), (90008, 449), (91670, 309),
  (95959, 485), (110789, 334)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y0_check. -/
theorem Z1Split76A0X0Y0_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y0_pairs. -/
theorem Z1Split76A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y1Certs : List (Nat × Nat) := [
  (1399, 756), (2397, 696), (16515, 714), (32167, 558), (41614, 580),
  (42118, 705), (42334, 579), (50891, 768), (53693, 713), (54098, 748),
  (60206, 723), (70116, 574), (81798, 664), (82423, 606), (86827, 642)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y1_check. -/
theorem Z1Split76A0X0Y1_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y1_pairs. -/
theorem Z1Split76A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split76A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y2Certs : List (Nat × Nat) := [
  (11966, 994), (13298, 798), (15488, 948), (24723, 854), (41344, 916),
  (48904, 995), (49952, 820), (51252, 823), (54465, 808), (60143, 919),
  (66702, 980)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y2_check. -/
theorem Z1Split76A0X0Y2_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y2_pairs. -/
theorem Z1Split76A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y2Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split76A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y3Certs : List (Nat × Nat) := [
  (922, 1097), (18603, 1183), (55752, 1130), (59506, 1243), (67691, 1061),
  (74918, 1084), (75501, 1239), (82942, 1128), (83383, 1145), (86053, 1045),
  (87399, 1179), (90794, 1295), (91592, 1294), (93293, 1063), (98240, 1205)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y3_check. -/
theorem Z1Split76A0X0Y3_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y3_pairs. -/
theorem Z1Split76A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y3Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split76A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y4Certs : List (Nat × Nat) := [
  (47, 1342), (11555, 1606), (18661, 1495), (20399, 1353), (45696, 1419),
  (51106, 1501), (59401, 1534), (62006, 1346), (68783, 1348), (83133, 1545),
  (110171, 1513), (112504, 1439)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y4_check. -/
theorem Z1Split76A0X0Y4_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y4_pairs. -/
theorem Z1Split76A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y4Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split76A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y5Certs : List (Nat × Nat) := [
  (21435, 1750), (25973, 1661), (29804, 1832), (34992, 1770), (47076, 1734),
  (67462, 1709)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y5_check. -/
theorem Z1Split76A0X0Y5_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y5_pairs. -/
theorem Z1Split76A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y5Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split76A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y6Certs : List (Nat × Nat) := [
  (154, 1932), (5937, 1993), (13934, 1923), (17550, 1929), (58604, 1904),
  (69492, 1947), (69791, 1946), (71897, 1950)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y6_check. -/
theorem Z1Split76A0X0Y6_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y6_pairs. -/
theorem Z1Split76A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y6Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split76A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y7Certs : List (Nat × Nat) := [
  (2726, 2182), (28033, 2150), (38188, 2203), (41710, 2171), (46537, 2142),
  (64341, 2316), (70166, 2284), (78308, 2303), (79760, 2191)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y7_check. -/
theorem Z1Split76A0X0Y7_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y7_pairs. -/
theorem Z1Split76A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y7Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split76A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y8Certs : List (Nat × Nat) := [
  (24647, 2403), (29790, 2558), (39072, 2421), (57667, 2414), (74550, 2430),
  (76095, 2544), (83424, 2493)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y8_check. -/
theorem Z1Split76A0X0Y8_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y8_pairs. -/
theorem Z1Split76A0X0Y8_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y8Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk8
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z1Split76A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y9Certs : List (Nat × Nat) := [
  (3030, 2593), (7634, 2639), (15542, 2626), (27150, 2806), (28687, 2850),
  (47123, 2765), (54327, 2776), (61775, 2691), (73889, 2699), (90436, 2651)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y9_check. -/
theorem Z1Split76A0X0Y9_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y9_pairs. -/
theorem Z1Split76A0X0Y9_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y9Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk9
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z1Split76A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X0Y10Certs : List (Nat × Nat) := [
  (6755, 3110), (7671, 3188), (23311, 3067), (23782, 3101), (24880, 3022),
  (27226, 2966), (29802, 3051), (34951, 2971), (55424, 3089), (65942, 3069),
  (74688, 3238), (90354, 3097), (98504, 3105)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y10_check. -/
theorem Z1Split76A0X0Y10_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0Y10_pairs. -/
theorem Z1Split76A0X0Y10_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X0Y10Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk0 masks3S512Chunk10
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z1Split76A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X0_pairs. -/
theorem Z1Split76A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z1Split76A0X0Y0_pairs x hx y hy hw
  · exact Z1Split76A0X0Y1_pairs x hx y hy hw
  · exact Z1Split76A0X0Y2_pairs x hx y hy hw
  · exact Z1Split76A0X0Y3_pairs x hx y hy hw
  · exact Z1Split76A0X0Y4_pairs x hx y hy hw
  · exact Z1Split76A0X0Y5_pairs x hx y hy hw
  · exact Z1Split76A0X0Y6_pairs x hx y hy hw
  · exact Z1Split76A0X0Y7_pairs x hx y hy hw
  · exact Z1Split76A0X0Y8_pairs x hx y hy hw
  · exact Z1Split76A0X0Y9_pairs x hx y hy hw
  · exact Z1Split76A0X0Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y0Certs : List (Nat × Nat) := [
  (38, 133), (15899, 501), (45809, 390), (72890, 202), (73876, 286)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y0_check. -/
theorem Z1Split76A0X1Y0_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y0_pairs. -/
theorem Z1Split76A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk0
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk0_bound y hy)
  · exact Z1Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y1Certs : List (Nat × Nat) := [
  (2044, 698), (5001, 747), (11392, 654), (14733, 733), (23459, 770),
  (33363, 624), (48854, 607), (62623, 635)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y1_check. -/
theorem Z1Split76A0X1Y1_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y1_pairs. -/
theorem Z1Split76A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y1Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk1
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk1_bound y hy)
  · exact Z1Split76A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y2Certs : List (Nat × Nat) := [
  (319, 998), (13347, 831), (29185, 806), (32731, 797), (51753, 936)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y2_check. -/
theorem Z1Split76A0X1Y2_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y2_pairs. -/
theorem Z1Split76A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y2Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk2
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk2_bound y hy)
  · exact Z1Split76A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y3Certs : List (Nat × Nat) := [
  (7527, 1258), (17388, 1156), (18657, 1211), (22770, 1276), (24043, 1036),
  (34435, 1032), (36764, 1272), (56494, 1064), (70863, 1049)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y3_check. -/
theorem Z1Split76A0X1Y3_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y3_pairs. -/
theorem Z1Split76A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y3Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk3
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk3_bound y hy)
  · exact Z1Split76A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y4Certs : List (Nat × Nat) := [
  (1842, 1570), (4830, 1623), (9057, 1533), (9610, 1596), (24323, 1378),
  (25292, 1379), (28224, 1395), (42288, 1403), (44743, 1438), (47670, 1474),
  (52557, 1498), (56395, 1483), (57040, 1595), (72110, 1625), (80125, 1488)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y4_check. -/
theorem Z1Split76A0X1Y4_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y4_pairs. -/
theorem Z1Split76A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y4Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk4
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk4_bound y hy)
  · exact Z1Split76A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y5Certs : List (Nat × Nat) := [
  (5794, 1833), (7750, 1653), (11998, 1718), (15831, 1692), (19014, 1818),
  (27771, 1740), (38746, 1701), (43889, 1643)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y5_check. -/
theorem Z1Split76A0X1Y5_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y5_pairs. -/
theorem Z1Split76A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y5Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk5
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk5_bound y hy)
  · exact Z1Split76A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y6Certs : List (Nat × Nat) := [
  (655, 1882), (2375, 2048), (13729, 1978), (14394, 2065), (15299, 2080),
  (21265, 2046), (23596, 1949), (42584, 2060), (43318, 1908)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y6_check. -/
theorem Z1Split76A0X1Y6_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y6_pairs. -/
theorem Z1Split76A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y6Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk6
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk6_bound y hy)
  · exact Z1Split76A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y7Certs : List (Nat × Nat) := [
  (4038, 2193), (16946, 2134), (24767, 2144), (28981, 2140), (41163, 2236),
  (43138, 2249), (44115, 2251), (46425, 2277), (46853, 2138)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y7_check. -/
theorem Z1Split76A0X1Y7_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y7_pairs. -/
theorem Z1Split76A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y7Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk7
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk7_bound y hy)
  · exact Z1Split76A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y8Certs : List (Nat × Nat) := [
  (516, 2458), (3138, 2569), (4871, 2559), (9034, 2506), (34623, 2491),
  (36921, 2393), (37553, 2575), (40006, 2573), (43116, 2549), (43177, 2360),
  (53779, 2401), (54445, 2379), (59454, 2426), (62419, 2548)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y8_check. -/
theorem Z1Split76A0X1Y8_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y8_pairs. -/
theorem Z1Split76A0X1Y8_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y8Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk8
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk8_bound y hy)
  · exact Z1Split76A0X1Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y9Certs : List (Nat × Nat) := [
  (11947, 2737), (21755, 2726), (22916, 2746), (28278, 2800), (28627, 2780),
  (29032, 2798), (32821, 2807), (32982, 2653), (39450, 2682), (42335, 2923),
  (48009, 2590), (50250, 2915), (57825, 2919)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y9_check. -/
theorem Z1Split76A0X1Y9_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y9_pairs. -/
theorem Z1Split76A0X1Y9_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y9Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk9
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk9_bound y hy)
  · exact Z1Split76A0X1Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split76A0X1Y10Certs : List (Nat × Nat) := [
  (34441, 3166), (41565, 3042), (45522, 2978), (47894, 3239), (63141, 3096),
  (63339, 2950), (65394, 2969), (67551, 3044), (68132, 3164), (69865, 2970),
  (70654, 2958), (73511, 2968)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y10_check. -/
theorem Z1Split76A0X1Y10_check : checkGrid m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1Y10_pairs. -/
theorem Z1Split76A0X1Y10_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 2 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      Z1M2LeftColumns Z1M2RightColumns) Z1Split76A0X1Y10Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M2Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TZ1 2 outerMasks2S256Chunk1 masks3S512Chunk10
      Z1M2LeftColumns Z1M2RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(Z1M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(Z1M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (Z1M2Right_columns_bound z hz).2 (by decide)⟩
    · exact Z1M2Left_eq
    · exact Z1M2Right_eq
    · intro x hx
      exact Z1M2Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M2Right_bound y (masks3S512Chunk10_bound y hy)
  · exact Z1Split76A0X1Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0X1_pairs. -/
theorem Z1Split76A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Z1Split76A0X1Y0_pairs x hx y hy hw
  · exact Z1Split76A0X1Y1_pairs x hx y hy hw
  · exact Z1Split76A0X1Y2_pairs x hx y hy hw
  · exact Z1Split76A0X1Y3_pairs x hx y hy hw
  · exact Z1Split76A0X1Y4_pairs x hx y hy hw
  · exact Z1Split76A0X1Y5_pairs x hx y hy hw
  · exact Z1Split76A0X1Y6_pairs x hx y hy hw
  · exact Z1Split76A0X1Y7_pairs x hx y hy hw
  · exact Z1Split76A0X1Y8_pairs x hx y hy hw
  · exact Z1Split76A0X1Y9_pairs x hx y hy hw
  · exact Z1Split76A0X1Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76A0_pairs. -/
theorem Z1Split76A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TZ1 2 x y 0) = 3 →
      sweepAccept m4TZ1 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split76A0X0_pairs x hx y hy hw
  · exact Z1Split76A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split76_check. -/
theorem Z1Split76_check : checkSplit m4TZ1 (3, 2, 3, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact Z1M2Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact Z1M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X0Y0Certs : List (Nat × Nat) := [
  (9243, 537), (15942, 1648), (18601, 2109), (18613, 2199), (19541, 2771),
  (19574, 3235), (43419, 2358), (65709, 129), (72598, 2627), (79520, 2297)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X0Y0_check. -/
theorem Z1Split77A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X0Y0_pairs. -/
theorem Z1Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk0 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X0_pairs. -/
theorem Z1Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X1Y0Certs : List (Nat × Nat) := [
  (188, 992), (715, 1644), (6637, 546), (7612, 1187), (24029, 507),
  (24973, 905), (24974, 908), (27021, 237), (36174, 332), (41917, 795),
  (46120, 76), (46181, 338), (47478, 299), (47774, 2375), (67432, 63),
  (69549, 2600), (70633, 812)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X1Y0_check. -/
theorem Z1Split77A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X1Y0_pairs. -/
theorem Z1Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk1 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X1_pairs. -/
theorem Z1Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X2Y0Certs : List (Nat × Nat) := [
  (12739, 601), (26966, 3151), (29993, 2964), (56251, 684), (56532, 2979),
  (81307, 2694), (81781, 37), (81857, 356), (81922, 699), (81944, 818),
  (81950, 865), (82213, 3177), (88390, 386)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X2Y0_check. -/
theorem Z1Split77A0X2Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X2Y0_pairs. -/
theorem Z1Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X2Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk2_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk2 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X2_pairs. -/
theorem Z1Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X3Y0Certs : List (Nat × Nat) := [
  (7523, 614), (18248, 2965), (24264, 2156), (25939, 1615), (31703, 2596),
  (54557, 923)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X3Y0_check. -/
theorem Z1Split77A0X3Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X3Y0_pairs. -/
theorem Z1Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X3Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk3_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk3 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X3_pairs. -/
theorem Z1Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X4Y0Certs : List (Nat × Nat) := [
  (720, 1665), (1478, 891), (3779, 1829), (6697, 889), (7434, 196),
  (13352, 1845), (28885, 897), (29803, 1215), (31399, 372), (54439, 302),
  (60239, 1141), (62059, 1680), (62060, 1686), (64261, 1910), (64947, 637)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X4Y0_check. -/
theorem Z1Split77A0X4Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X4Y0_pairs. -/
theorem Z1Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X4Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk4_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk4 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X4_pairs. -/
theorem Z1Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X5Y0Certs : List (Nat × Nat) := [
  (5852, 1023), (31480, 804), (42231, 191), (49637, 226), (49753, 813),
  (51480, 755), (51750, 3012)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X5Y0_check. -/
theorem Z1Split77A0X5Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X5Y0_pairs. -/
theorem Z1Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X5Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk5_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk5 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X5_pairs. -/
theorem Z1Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X6Y0Certs : List (Nat × Nat) := [
  (3102, 282), (3198, 787), (13155, 530), (16435, 2167), (19287, 721),
  (19305, 834), (19395, 1467), (19491, 2349), (19546, 2945), (19548, 2948),
  (21355, 198), (29654, 350), (31875, 593)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X6Y0_check. -/
theorem Z1Split77A0X6Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X6Y0_pairs. -/
theorem Z1Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X6Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk6_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk6 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X6_pairs. -/
theorem Z1Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X7Y0Certs : List (Nat × Nat) := [
  (1973, 1311), (1983, 1351), (40185, 833), (40426, 2944), (41565, 1334),
  (49227, 340), (49524, 2445), (54498, 598), (54670, 1736), (61694, 2376),
  (64769, 2635), (69254, 429)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X7Y0_check. -/
theorem Z1Split77A0X7Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X7Y0_pairs. -/
theorem Z1Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X7Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk7_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk7 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X7_pairs. -/
theorem Z1Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X8Y0Certs : List (Nat × Nat) := [
  (5820, 832), (5925, 1543), (6008, 2354), (6012, 2366), (6061, 2943),
  (6067, 2960), (9052, 2351), (17920, 389), (18011, 900), (19726, 762),
  (20248, 1323), (20289, 1639), (37122, 719), (37230, 1466), (77714, 1659),
  (78752, 109), (78871, 687), (78905, 863), (78988, 1460), (79000, 1506),
  (79152, 2982), (88489, 932)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X8Y0_check. -/
theorem Z1Split77A0X8Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X8Y0_pairs. -/
theorem Z1Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X8Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk8_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk8 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X8_pairs. -/
theorem Z1Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X9Y0Certs : List (Nat × Nat) := [
  (6849, 2056), (20430, 3013), (26787, 1433), (28623, 2270), (28884, 893),
  (28903, 1014), (31565, 1361), (38782, 326), (50114, 428), (59560, 2741),
  (60225, 1019), (63427, 2352), (64117, 890), (67134, 710), (71377, 194),
  (71674, 2129), (71828, 247), (74634, 1398), (105128, 1723)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X9Y0_check. -/
theorem Z1Split77A0X9Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X9Y0_pairs. -/
theorem Z1Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X9Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk9_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk9 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X9_pairs. -/
theorem Z1Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X10Y0Certs : List (Nat × Nat) := [
  (2057, 1926), (2116, 2557), (13121, 339), (21044, 815), (21313, 3174),
  (22933, 1887), (71853, 369), (76934, 2500), (76978, 2994), (86321, 1010),
  (86355, 1233), (87977, 535), (97995, 594), (98001, 608), (99816, 1047),
  (99888, 1605)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X10Y0_check. -/
theorem Z1Split77A0X10Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X10Y0_pairs. -/
theorem Z1Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X10Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk10_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk10 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X10_pairs. -/
theorem Z1Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X11Y0_check. -/
theorem Z1Split77A0X11Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X11Y0_pairs. -/
theorem Z1Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X11Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk11_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk11 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X11_pairs. -/
theorem Z1Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X12Y0Certs : List (Nat × Nat) := [
  (12632, 106), (12763, 730), (12779, 816), (12880, 1507), (12886, 1568),
  (13048, 3175), (17401, 38), (17542, 700), (37450, 201), (37523, 549),
  (41101, 1167), (41194, 1850), (42407, 1171), (44543, 892), (47630, 1180),
  (51822, 283), (51826, 289), (51918, 785), (52035, 1541), (52122, 2367),
  (52173, 2949), (56229, 556), (68076, 1185), (69332, 851), (70105, 336),
  (72443, 1310)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X12Y0_check. -/
theorem Z1Split77A0X12Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X12Y0_pairs. -/
theorem Z1Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X12Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk12_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk12 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X12_pairs. -/
theorem Z1Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X13Y0Certs : List (Nat × Nat) := [
  (3549, 331)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X13Y0_check. -/
theorem Z1Split77A0X13Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X13Y0_pairs. -/
theorem Z1Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X13Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk13_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk13 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X13_pairs. -/
theorem Z1Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X14Y0Certs : List (Nat × Nat) := [
  (22677, 281), (22697, 355), (22773, 786), (22994, 2503), (23032, 2961),
  (23038, 2993), (26019, 2357), (28694, 3008), (33470, 2953), (50209, 930),
  (50311, 1670), (50861, 2772), (53344, 1614), (53964, 131), (54278, 2149),
  (80310, 1542), (80397, 2368), (95041, 1168)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X14Y0_check. -/
theorem Z1Split77A0X14Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X14Y0_pairs. -/
theorem Z1Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X14Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk14_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk14 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X14_pairs. -/
theorem Z1Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X15Y0Certs : List (Nat × Nat) := [
  (15754, 446), (17037, 343), (17112, 720), (17218, 1461), (17220, 1465),
  (17318, 2353), (17334, 2448), (29005, 1738)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X15Y0_check. -/
theorem Z1Split77A0X15Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X15Y0_pairs. -/
theorem Z1Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X15Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk15_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk15 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X15_pairs. -/
theorem Z1Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X16Y0Certs : List (Nat × Nat) := [
  (2877, 1522), (23979, 252), (25337, 534), (26641, 533), (26656, 595),
  (29961, 2588), (54141, 1048), (59269, 539), (59270, 542), (64162, 1186),
  (64706, 2093), (66476, 2365), (66689, 649), (67708, 1651), (67732, 1857),
  (72120, 2216), (81937, 794), (98498, 991)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X16Y0_check. -/
theorem Z1Split77A0X16Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X16Y0_pairs. -/
theorem Z1Split77A0X16Y0_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X16Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk16_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk16 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk16_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X16_pairs. -/
theorem Z1Split77A0X16_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X17Y0Certs : List (Nat × Nat) := [
  (1203, 2119), (2920, 1875), (4960, 896), (6935, 2954), (7675, 1645),
  (11200, 2091), (36236, 633), (38536, 1470)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X17Y0_check. -/
theorem Z1Split77A0X17Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X17Y0_pairs. -/
theorem Z1Split77A0X17Y0_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X17Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk17_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk17 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk17_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X17_pairs. -/
theorem Z1Split77A0X17_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X18Y0Certs : List (Nat × Nat) := [
  (9202, 327), (28900, 1007), (39747, 809), (41397, 341), (41461, 685),
  (41596, 1567), (41676, 2350), (41694, 2446), (41742, 2980), (49607, 108),
  (49855, 1505), (74716, 2108), (80589, 554), (80699, 1222), (85702, 62),
  (86082, 2624), (87886, 105), (90327, 1649), (95311, 224), (100051, 35),
  (100111, 291), (100192, 701), (100198, 731), (100424, 2502), (100468, 2996),
  (107235, 1234)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X18Y0_check. -/
theorem Z1Split77A0X18Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X18Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X18Y0_pairs. -/
theorem Z1Split77A0X18Y0_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X18Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk18_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk18 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk18_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X18Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X18_pairs. -/
theorem Z1Split77A0X18_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X18Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X19Y0Certs : List (Nat × Nat) := [
  (12459, 1641), (48880, 803)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X19Y0_check. -/
theorem Z1Split77A0X19Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X19Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X19Y0_pairs. -/
theorem Z1Split77A0X19Y0_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X19Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk19_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk19 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk19_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X19Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X19_pairs. -/
theorem Z1Split77A0X19_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X19Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X20Y0Certs : List (Nat × Nat) := [
  (686, 1409), (6606, 373), (6916, 2641), (7842, 81), (16901, 2478),
  (24511, 763), (33695, 1039), (60165, 661), (61583, 1391), (62421, 1184),
  (64168, 1216), (64594, 1178), (64615, 1315), (66860, 1853), (69200, 175),
  (71579, 1329), (86208, 370), (101219, 1828), (103018, 2373), (104717, 1927)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X20Y0_check. -/
theorem Z1Split77A0X20Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X20Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X20Y0_pairs. -/
theorem Z1Split77A0X20Y0_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X20Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk20_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk20 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk20_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X20Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X20_pairs. -/
theorem Z1Split77A0X20_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X20Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split77A0X21Y0Certs : List (Nat × Nat) := [
  (1089, 1196), (1090, 1201), (4893, 536), (7474, 371), (7844, 83),
  (9986, 2976), (20046, 192), (45336, 450), (47527, 545), (48244, 2672),
  (50310, 1664), (51829, 301), (52674, 197)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X21Y0_check. -/
theorem Z1Split77A0X21Y0_check : checkGrid m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X21Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X21Y0_pairs. -/
theorem Z1Split77A0X21Y0_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split77A0X21Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk21_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S256Chunk21 masks2S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk21_bound
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
      exact Z1M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact Z1Split77A0X21Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0X21_pairs. -/
theorem Z1Split77A0X21_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split77A0X21Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77A0_pairs. -/
theorem Z1Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 3 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact Z1Split77A0X0_pairs x hx y hy hw
  · exact Z1Split77A0X1_pairs x hx y hy hw
  · exact Z1Split77A0X2_pairs x hx y hy hw
  · exact Z1Split77A0X3_pairs x hx y hy hw
  · exact Z1Split77A0X4_pairs x hx y hy hw
  · exact Z1Split77A0X5_pairs x hx y hy hw
  · exact Z1Split77A0X6_pairs x hx y hy hw
  · exact Z1Split77A0X7_pairs x hx y hy hw
  · exact Z1Split77A0X8_pairs x hx y hy hw
  · exact Z1Split77A0X9_pairs x hx y hy hw
  · exact Z1Split77A0X10_pairs x hx y hy hw
  · exact Z1Split77A0X11_pairs x hx y hy hw
  · exact Z1Split77A0X12_pairs x hx y hy hw
  · exact Z1Split77A0X13_pairs x hx y hy hw
  · exact Z1Split77A0X14_pairs x hx y hy hw
  · exact Z1Split77A0X15_pairs x hx y hy hw
  · exact Z1Split77A0X16_pairs x hx y hy hw
  · exact Z1Split77A0X17_pairs x hx y hy hw
  · exact Z1Split77A0X18_pairs x hx y hy hw
  · exact Z1Split77A0X19_pairs x hx y hy hw
  · exact Z1Split77A0X20_pairs x hx y hy hw
  · exact Z1Split77A0X21_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split77_check. -/
theorem Z1Split77_check : checkSplit m4TZ1 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split78A0X0Y0Certs : List (Nat × Nat) := [
  (1286, 2087), (1348, 2579), (6644, 440), (7075, 1837), (9785, 75),
  (9878, 153), (13860, 2), (14766, 95), (19290, 12), (19292, 32),
  (19308, 775), (24938, 150), (25010, 1001), (26548, 2577), (29801, 261),
  (31523, 1453), (32500, 218), (32624, 442), (35531, 272), (35537, 678),
  (35549, 2941), (40042, 1308), (41028, 779), (41102, 25), (43182, 318),
  (43655, 69), (43657, 115), (46596, 88), (46602, 321), (46608, 783),
  (47452, 1305), (47454, 1630), (47590, 220), (47593, 366), (51630, 4),
  (51632, 22), (51636, 94)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X0Y0_check. -/
theorem Z1Split78A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X0Y0_pairs. -/
theorem Z1Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split78A0X0Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S2048Chunk0 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
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
      exact Z1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X0_pairs. -/
theorem Z1Split78A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split78A0X1Y0Certs : List (Nat × Nat) := [
  (145, 1842), (2459, 2942), (2567, 671), (5367, 2345), (5944, 53),
  (5948, 149), (6766, 590), (6890, 1004), (9173, 1449), (9177, 2339),
  (9179, 2932), (10881, 1160), (10885, 1841), (11109, 186), (11114, 439),
  (11861, 274), (11867, 670), (11873, 1458), (18840, 9), (18852, 312),
  (18858, 784), (20733, 43), (20756, 2081), (21016, 588), (21019, 886),
  (26042, 23), (26046, 93), (26052, 320), (31450, 223), (34972, 1303),
  (40421, 266), (40437, 2343), (40439, 2937), (43111, 16), (43138, 2576),
  (43485, 526), (43490, 1006), (44477, 681), (44483, 1447), (44487, 2335),
  (56825, 72), (57016, 587), (59966, 2082)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X1Y0_check. -/
theorem Z1Split78A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split78A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X1Y0_pairs. -/
theorem Z1Split78A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split78A0X1Y0Certs
  · exact censusZ1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact Z1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TZ1 0 outerMasks3S2048Chunk1 masks1S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
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
      exact Z1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact Z1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact Z1Split78A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0X1_pairs. -/
theorem Z1Split78A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split78A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78A0_pairs. -/
theorem Z1Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 4 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split78A0X0_pairs x hx y hy hw
  · exact Z1Split78A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split78_check. -/
theorem Z1Split78_check : checkSplit m4TZ1 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact Z1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact Z1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact Z1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact Z1Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X0Y0_check. -/
theorem Z1Split79A0X0Y0_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X0Y0_pairs. -/
theorem Z1Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split79A0X0Y0Certs
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
  · exact Z1Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X0_pairs. -/
theorem Z1Split79A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def Z1Split79A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X1Y0_check. -/
theorem Z1Split79A0X1Y0_check : checkGrid m4TZ1 censusZ1 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split79A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X1Y0_pairs. -/
theorem Z1Split79A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  apply checkGrid_sound m4TZ1 censusZ1 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      Z1M0LeftColumns Z1M0RightColumns) Z1Split79A0X1Y0Certs
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
  · exact Z1Split79A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0X1_pairs. -/
theorem Z1Split79A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact Z1Split79A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79A0_pairs. -/
theorem Z1Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TZ1 0 x y 0) = 5 →
      sweepAccept m4TZ1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact Z1Split79A0X0_pairs x hx y hy hw
  · exact Z1Split79A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1Split79_check. -/
theorem Z1Split79_check : checkSplit m4TZ1 (3, 5, 0, 0) = true := by
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
    · exact Z1Split79A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

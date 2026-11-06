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
def X0Split64A0X0Y0Certs : List (Nat × Nat) := [
  (167, 613), (174, 644), (580, 530), (588, 567), (599, 593),
  (798, 1538), (868, 1983), (1060, 724), (1153, 1120), (1583, 1106),
  (1613, 1249), (1741, 30), (1876, 505), (2008, 1050), (2157, 1856),
  (2164, 1891), (2299, 458), (2361, 687), (2400, 846), (2452, 1102),
  (2454, 1109), (2691, 306), (2912, 1235), (3063, 101), (3437, 1700),
  (3546, 262), (3865, 1672), (3932, 96), (3970, 226), (4062, 535),
  (4170, 1004), (4287, 1605), (4359, 64), (4374, 119), (4561, 800),
  (4590, 914), (4647, 1190), (5048, 1023), (5107, 1319), (5132, 1450),
  (5168, 1665), (5171, 1678), (5398, 653), (5604, 1669), (5728, 278),
  (5853, 736), (6176, 321), (6245, 571), (6597, 275), (6663, 508),
  (6795, 1062), (6882, 1516), (6932, 1833), (6964, 40), (6967, 62),
  (7003, 175), (7045, 314), (7300, 1398), (7448, 209), (7494, 362),
  (7725, 1369), (7762, 1555), (7799, 1786), (7904, 282), (8119, 1140),
  (8431, 606), (8579, 1265), (8715, 92), (8885, 676), (9194, 237),
  (9300, 599), (9394, 1012), (9509, 1624), (9553, 1858), (9595, 122),
  (9610, 168), (9688, 429), (9754, 670), (9785, 808), (10038, 140),
  (10055, 202), (10139, 485), (10209, 754), (10433, 1919), (10611, 639),
  (10838, 1731), (10943, 266), (11171, 1178), (11356, 193), (11397, 325),
  (11424, 415), (11539, 867), (11605, 1168), (11846, 367), (11875, 473),
  (11996, 975), (12065, 1302), (12081, 1385), (12339, 577), (12483, 1237),
  (12756, 515), (12821, 765), (12862, 950), (12965, 1479), (13018, 1774)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0X0Y0_check. -/
theorem X0Split64A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0X0Y0_pairs. -/
theorem X0Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split64A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0X0_pairs. -/
theorem X0Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split64A0_pairs. -/
theorem X0Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split64_check. -/
theorem X0Split64_check : checkSplit m4TX0 (1, 5, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split65A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0X0Y0_check. -/
theorem X0Split65A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0X0Y0_pairs. -/
theorem X0Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split65A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0X0_pairs. -/
theorem X0Split65A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split65A0_pairs. -/
theorem X0Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split65_check. -/
theorem X0Split65_check : checkSplit m4TX0 (1, 6, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0X0Y0_check. -/
theorem X0Split66A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0X0Y0_pairs. -/
theorem X0Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split66A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X0Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0X0_pairs. -/
theorem X0Split66A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split66A0_pairs. -/
theorem X0Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 7 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split66_check. -/
theorem X0Split66_check : checkSplit m4TX0 (1, 7, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split67A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0X0Y0_check. -/
theorem X0Split67A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0X0Y0_pairs. -/
theorem X0Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split67A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0X0_pairs. -/
theorem X0Split67A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split67A0_pairs. -/
theorem X0Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 6 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split67_check. -/
theorem X0Split67_check : checkSplit m4TX0 (2, 0, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split67A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split68A0X0Y0Certs : List (Nat × Nat) := [
  (493, 1297), (1347, 815), (1852, 1613), (2119, 1766), (2134, 1815),
  (2397, 1453), (2510, 1186), (3153, 1867), (3257, 1565), (3599, 334),
  (3615, 1396), (4466, 1915), (4884, 1637), (4899, 1961), (5279, 1449),
  (5455, 1327), (5470, 1973), (5865, 1987), (6036, 1765), (6367, 751),
  (6533, 1933), (6911, 702), (7011, 776), (7028, 839), (7174, 1092),
  (7702, 1884), (8135, 1060), (8561, 1026), (8788, 1798), (8806, 1811),
  (9047, 1214), (9321, 1978), (9522, 1635), (9931, 1338), (9974, 683),
  (10179, 1650), (10540, 1622), (10766, 1046), (10770, 1442), (11483, 1426),
  (11821, 556), (12048, 1930), (12256, 1980), (12575, 1601), (12602, 1286)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0X0Y0_check. -/
theorem X0Split68A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0X0Y0_pairs. -/
theorem X0Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split68A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0X0_pairs. -/
theorem X0Split68A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split68A0_pairs. -/
theorem X0Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split68_check. -/
theorem X0Split68_check : checkSplit m4TX0 (2, 1, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split68A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split69A0X0Y0Certs : List (Nat × Nat) := [
  (1924, 1956), (2374, 1467), (5475, 988), (6674, 376), (9186, 1710),
  (11170, 597), (12060, 1608), (13244, 1632), (13924, 1726), (14675, 1751),
  (15351, 1923), (19265, 821), (19608, 1294), (22542, 1462), (23997, 1488),
  (26741, 1025), (27013, 1647), (29119, 1785), (29852, 783), (31247, 1591),
  (34624, 555), (34932, 853), (35429, 744), (38124, 540), (39549, 1859),
  (39851, 1614), (40154, 1873), (41039, 969), (42504, 1886), (43525, 1148),
  (44338, 1145), (45483, 1404), (47035, 1921), (52006, 420), (52464, 1412),
  (53171, 1741), (57838, 1561), (60195, 1734), (60520, 1185), (64702, 1564),
  (64933, 1887), (67487, 1794), (67872, 1312), (69134, 749), (69540, 1346),
  (70178, 1053), (71328, 1962), (75908, 1581), (76488, 1091), (77244, 945),
  (77739, 1283), (79276, 1335), (80934, 1072), (82244, 623), (83890, 1931),
  (84641, 857), (84912, 1059), (85967, 1461), (86181, 127), (88263, 1056),
  (89262, 711), (89996, 681), (91258, 875), (94533, 1387), (94883, 1609),
  (100391, 851), (101723, 958), (103301, 1342), (103969, 1611), (108479, 1927)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X0Y0_check. -/
theorem X0Split69A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X0Y0_pairs. -/
theorem X0Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X0_pairs. -/
theorem X0Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split69A0X1Y0Certs : List (Nat × Nat) := [
  (1342, 1940), (2763, 1259), (3183, 1288), (8234, 1932), (8494, 1057),
  (10100, 960), (13142, 1902), (13547, 1414), (14344, 1649), (15214, 682),
  (15550, 1443), (16053, 1762), (17614, 1812), (19225, 1587), (21116, 932),
  (23485, 1482), (24250, 1175), (24710, 961), (24981, 1621), (26475, 1560),
  (26667, 338), (28493, 1617), (29766, 1183), (30114, 1184), (30895, 1219),
  (31456, 1417), (34359, 1465), (36862, 1702), (37435, 1888), (42663, 1403),
  (45784, 1549), (47851, 1718), (48544, 1693), (53347, 1618), (54467, 1950),
  (55107, 1262), (55727, 1557), (56450, 1427), (59653, 1721), (60477, 1196),
  (61283, 1468), (61632, 1979), (63049, 1926), (63324, 709), (65889, 1273),
  (67526, 860), (67869, 1951), (72429, 1911), (74402, 980), (75183, 610)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X1Y0_check. -/
theorem X0Split69A0X1Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X1Y0_pairs. -/
theorem X0Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split69A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0X1_pairs. -/
theorem X0Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69A0_pairs. -/
theorem X0Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split69A0X0_pairs x hx y hy hw
  · exact X0Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split69_check. -/
theorem X0Split69_check : checkSplit m4TX0 (2, 2, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split69A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y0Certs : List (Nat × Nat) := [
  (7277, 377), (64705, 172), (69487, 328), (70607, 146), (90144, 128),
  (101706, 281), (103464, 240), (112938, 173)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y0_check. -/
theorem X0Split70A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y0_pairs. -/
theorem X0Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X0Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y1Certs : List (Nat × Nat) := [
  (15150, 554), (22443, 426), (27458, 410), (29767, 478), (36146, 418),
  (56697, 407), (70490, 437), (75784, 550)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y1_check. -/
theorem X0Split70A0X0Y1_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y1_pairs. -/
theorem X0Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y1Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X0Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y2Certs : List (Nat × Nat) := [
  (34789, 621), (36306, 582), (55808, 608), (69864, 664), (75034, 659)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y2_check. -/
theorem X0Split70A0X0Y2_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y2_pairs. -/
theorem X0Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y2Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X0Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y3Certs : List (Nat × Nat) := [
  (5928, 859), (8229, 819), (13031, 820), (14666, 834), (16737, 862),
  (27387, 784), (32538, 772), (59938, 863), (67872, 837), (68074, 748),
  (82314, 848), (87517, 852)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y3_check. -/
theorem X0Split70A0X0Y3_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y3_pairs. -/
theorem X0Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y3Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X0Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y4Certs : List (Nat × Nat) := [
  (13514, 1084), (26383, 1014), (29571, 921), (44607, 936), (55000, 1038),
  (56028, 1065), (56131, 1090), (59189, 956), (60172, 966), (63684, 1024),
  (78265, 1052), (87266, 962), (91088, 944), (97087, 1029), (104550, 904),
  (105317, 1030), (120660, 959)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y4_check. -/
theorem X0Split70A0X0Y4_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y4_pairs. -/
theorem X0Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y4Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X0Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y5Certs : List (Nat × Nat) := [
  (10832, 1136), (12828, 1161), (65946, 1218), (67706, 1144)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y5_check. -/
theorem X0Split70A0X0Y5_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y5_pairs. -/
theorem X0Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y5Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X0Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y6Certs : List (Nat × Nat) := [
  (17862, 1289), (47998, 1347), (53659, 1330)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y6_check. -/
theorem X0Split70A0X0Y6_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y6_pairs. -/
theorem X0Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y6Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X0Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y7Certs : List (Nat × Nat) := [
  (1776, 1421), (14756, 1411), (18739, 1447), (21150, 1373), (21813, 1380),
  (29053, 1410), (33864, 1386), (37975, 1472), (40163, 1436), (42582, 1366),
  (48226, 1409), (63225, 1431), (77288, 1460), (78021, 1372)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y7_check. -/
theorem X0Split70A0X0Y7_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y7_pairs. -/
theorem X0Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y7Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X0Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y8Certs : List (Nat × Nat) := [
  (4407, 1598), (27872, 1571), (31636, 1529), (32161, 1610), (47455, 1540),
  (74999, 1620), (77604, 1522), (78794, 1582), (79583, 1627), (79666, 1648),
  (80007, 1646), (87177, 1562)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y8_check. -/
theorem X0Split70A0X0Y8_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y8_pairs. -/
theorem X0Split70A0X0Y8_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y8Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk8
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact X0Split70A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y9Certs : List (Nat × Nat) := [
  (25276, 1790), (29203, 1701), (48562, 1724), (50027, 1717), (53570, 1764),
  (54915, 1708), (90556, 1744)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y9_check. -/
theorem X0Split70A0X0Y9_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y9_pairs. -/
theorem X0Split70A0X0Y9_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y9Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk9
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact X0Split70A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X0Y10Certs : List (Nat × Nat) := [
  (9267, 1977), (14445, 1920), (21016, 1969), (39203, 1914), (44141, 1957),
  (47422, 1976), (55723, 1868), (56688, 1936), (64389, 1924), (70805, 1897),
  (71316, 1944), (71583, 1879), (76858, 1878), (77799, 1935), (78073, 1877),
  (94407, 1913), (94552, 1984), (102474, 1898)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y10_check. -/
theorem X0Split70A0X0Y10_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0Y10_pairs. -/
theorem X0Split70A0X0Y10_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X0Y10Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks3S512Chunk10
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact X0Split70A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X0_pairs. -/
theorem X0Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact X0Split70A0X0Y0_pairs x hx y hy hw
  · exact X0Split70A0X0Y1_pairs x hx y hy hw
  · exact X0Split70A0X0Y2_pairs x hx y hy hw
  · exact X0Split70A0X0Y3_pairs x hx y hy hw
  · exact X0Split70A0X0Y4_pairs x hx y hy hw
  · exact X0Split70A0X0Y5_pairs x hx y hy hw
  · exact X0Split70A0X0Y6_pairs x hx y hy hw
  · exact X0Split70A0X0Y7_pairs x hx y hy hw
  · exact X0Split70A0X0Y8_pairs x hx y hy hw
  · exact X0Split70A0X0Y9_pairs x hx y hy hw
  · exact X0Split70A0X0Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y0Certs : List (Nat × Nat) := [
  (14069, 371), (28116, 340), (34791, 253), (39243, 179), (39883, 312),
  (54525, 358), (63248, 44)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y0_check. -/
theorem X0Split70A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y0_pairs. -/
theorem X0Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X0Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y1Certs : List (Nat × Nat) := [
  (640, 532), (4381, 422), (26408, 424), (34349, 423), (36992, 479),
  (50588, 421), (56070, 462), (59079, 517), (62791, 551)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y1_check. -/
theorem X0Split70A0X1Y1_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y1_pairs. -/
theorem X0Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y1Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk1
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X0Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y2Certs : List (Nat × Nat) := [
  (7396, 693), (8916, 651), (30055, 680), (47301, 713)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y2_check. -/
theorem X0Split70A0X1Y2_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y2_pairs. -/
theorem X0Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y2Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk2
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X0Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y3Certs : List (Nat × Nat) := [
  (1731, 768), (6220, 817), (23189, 879), (41525, 858), (46719, 854),
  (61670, 746), (70062, 745)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y3_check. -/
theorem X0Split70A0X1Y3_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y3_pairs. -/
theorem X0Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y3Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk3
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X0Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y4Certs : List (Nat × Nat) := [
  (8783, 930), (9581, 1070), (11196, 927), (16061, 940), (25711, 926),
  (28527, 1086), (32949, 916), (34815, 1085), (49734, 1061), (74158, 949),
  (76476, 901), (78560, 964), (79103, 986), (83595, 1054)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y4_check. -/
theorem X0Split70A0X1Y4_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y4_pairs. -/
theorem X0Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y4Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk4
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X0Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y5Certs : List (Nat × Nat) := [
  (14549, 1182), (15390, 1193), (15497, 1130), (20533, 1155), (34450, 1204)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y5_check. -/
theorem X0Split70A0X1Y5_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y5_pairs. -/
theorem X0Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y5Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk5
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X0Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y6Certs : List (Nat × Nat) := [
  (167, 1292), (25049, 1285), (30425, 1279), (32348, 1325), (40581, 1261),
  (42406, 1268), (47730, 1251)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y6_check. -/
theorem X0Split70A0X1Y6_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y6_pairs. -/
theorem X0Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y6Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk6
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X0Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y7Certs : List (Nat × Nat) := [
  (12619, 1469), (15150, 1440), (23667, 1466), (32013, 1424), (33696, 1448),
  (41059, 1401), (44670, 1420)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y7_check. -/
theorem X0Split70A0X1Y7_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y7_pairs. -/
theorem X0Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y7Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk7
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X0Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y8Certs : List (Nat × Nat) := [
  (2516, 1534), (3794, 1631), (11414, 1588), (12161, 1615), (17958, 1533),
  (22253, 1569), (28196, 1551), (29609, 1558), (29883, 1530), (42828, 1513),
  (45049, 1556), (50033, 1596), (57114, 1623)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y8_check. -/
theorem X0Split70A0X1Y8_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y8_pairs. -/
theorem X0Split70A0X1Y8_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y8Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk8
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact X0Split70A0X1Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y9Certs : List (Nat × Nat) := [
  (13971, 1805), (37990, 1732), (42400, 1690), (60721, 1757), (63852, 1802)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y9_check. -/
theorem X0Split70A0X1Y9_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y9_pairs. -/
theorem X0Split70A0X1Y9_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y9Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk9
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact X0Split70A0X1Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split70A0X1Y10Certs : List (Nat × Nat) := [
  (456, 1852), (3552, 1967), (30972, 1874), (38816, 1928), (45211, 1885),
  (46378, 1866), (54546, 1882), (59944, 1941), (63374, 1849)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y10_check. -/
theorem X0Split70A0X1Y10_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1Y10_pairs. -/
theorem X0Split70A0X1Y10_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      X0M0LeftColumns X0M0RightColumns) X0Split70A0X1Y10Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks3S512Chunk10
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact X0Split70A0X1Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0X1_pairs. -/
theorem X0Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact X0Split70A0X1Y0_pairs x hx y hy hw
  · exact X0Split70A0X1Y1_pairs x hx y hy hw
  · exact X0Split70A0X1Y2_pairs x hx y hy hw
  · exact X0Split70A0X1Y3_pairs x hx y hy hw
  · exact X0Split70A0X1Y4_pairs x hx y hy hw
  · exact X0Split70A0X1Y5_pairs x hx y hy hw
  · exact X0Split70A0X1Y6_pairs x hx y hy hw
  · exact X0Split70A0X1Y7_pairs x hx y hy hw
  · exact X0Split70A0X1Y8_pairs x hx y hy hw
  · exact X0Split70A0X1Y9_pairs x hx y hy hw
  · exact X0Split70A0X1Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70A0_pairs. -/
theorem X0Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split70A0X0_pairs x hx y hy hw
  · exact X0Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split70_check. -/
theorem X0Split70_check : checkSplit m4TX0 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split71A0X0Y0Certs : List (Nat × Nat) := [
  (239, 910), (609, 645), (3451, 1828), (3462, 1854), (3819, 1390),
  (6006, 1506), (6306, 809), (6364, 1083), (6705, 657), (7678, 1121),
  (7842, 80), (8985, 1125), (10748, 1250), (14179, 1013), (14353, 1981),
  (16243, 538), (16248, 566), (17457, 231), (17547, 534), (18045, 797),
  (18465, 731), (19662, 323), (19800, 844), (21961, 798), (21963, 802),
  (23028, 1834), (23557, 264), (23842, 1508), (27513, 395), (28609, 1379),
  (28613, 1389), (28732, 116), (29871, 1154), (31401, 307), (31806, 205),
  (32583, 1707), (33168, 393), (35551, 1275), (37367, 1699), (37472, 246),
  (39109, 1711), (43131, 263), (43863, 1537), (43917, 1855), (46182, 274),
  (46518, 1835), (47416, 29), (47686, 1068), (49216, 243), (49732, 519),
  (49860, 1063), (50027, 31), (50783, 1329), (51205, 1257), (53256, 686),
  (53281, 799), (54550, 648), (54654, 1108), (56557, 61), (56572, 115),
  (57313, 1365), (57916, 241), (58882, 574), (59135, 1840), (60017, 1876),
  (60021, 1907), (60671, 764), (60812, 1451), (64275, 1368), (64278, 1374),
  (65467, 810), (66230, 401), (66296, 650), (66844, 1139), (67507, 308),
  (68755, 121), (68844, 417), (69378, 804), (71953, 652), (72342, 480),
  (72863, 816), (73732, 811), (74634, 965), (75786, 357), (77830, 1754),
  (80238, 735), (80624, 544), (82019, 909), (82742, 350), (83356, 1067),
  (86395, 1033), (88895, 572), (89322, 533), (89599, 1892), (92154, 1575),
  (92218, 1982), (93151, 242), (93255, 600), (95282, 97), (95616, 1504),
  (96496, 1527), (96500, 1546), (97588, 537), (98140, 1035), (98249, 1625),
  (98329, 102), (99150, 1804), (99574, 1713), (100564, 304), (100995, 286),
  (102844, 671), (102877, 812), (103102, 60), (103392, 1191), (104859, 118),
  (105120, 1127), (107485, 169), (107527, 310), (107906, 125), (108898, 539),
  (109656, 159), (109684, 249)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X0Y0_check. -/
theorem X0Split71A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X0Y0_pairs. -/
theorem X0Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X0_pairs. -/
theorem X0Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split71A0X1Y0Certs : List (Nat × Nat) := [
  (849, 1847), (1982, 925), (2051, 1260), (3367, 1317), (3375, 1367),
  (5095, 1256), (5171, 1676), (7445, 204), (7491, 355), (8779, 303),
  (9790, 826), (9856, 1132), (11200, 1360), (11708, 1730), (13250, 740),
  (14891, 365), (15037, 952), (15993, 1375), (18584, 1264), (18977, 1077),
  (20349, 1392), (21509, 730), (22125, 1630), (22536, 1505), (23982, 233),
  (26904, 1577), (29160, 93), (29635, 228), (29850, 1064), (31862, 392),
  (31906, 548), (32365, 647), (33228, 616), (33720, 845), (33786, 1152),
  (35749, 305), (35965, 1169), (36544, 42), (36580, 170), (38365, 315),
  (38388, 394), (41004, 416), (41070, 658), (41413, 330), (42031, 1069),
  (44130, 733), (44472, 370), (44992, 696), (46887, 1419), (46940, 1719),
  (47735, 1300), (47754, 1391), (48335, 203), (48689, 1788), (50124, 360),
  (50419, 1712), (52765, 474), (52835, 741), (53680, 646), (54061, 455),
  (54063, 457), (54948, 510), (55184, 1626), (57294, 1253), (57829, 1838),
  (58014, 578), (58698, 1836), (60607, 518), (63481, 1830), (65318, 265),
  (68965, 902), (68968, 907), (69910, 1255), (70677, 771), (71203, 1207),
  (71687, 1452), (71740, 1753), (73338, 1009), (73341, 1016), (74145, 732),
  (74353, 1772), (74853, 141), (74950, 475), (76764, 752), (76799, 908),
  (78547, 951), (78616, 1276), (79020, 1126)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X1Y0_check. -/
theorem X0Split71A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X1Y0_pairs. -/
theorem X0Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split71A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0X1_pairs. -/
theorem X0Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71A0_pairs. -/
theorem X0Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split71A0X0_pairs x hx y hy hw
  · exact X0Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split71_check. -/
theorem X0Split71_check : checkSplit m4TX0 (2, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split72A0X0Y0Certs : List (Nat × Nat) := [
  (364, 45), (987, 1502), (1139, 1818), (1365, 387), (1382, 23),
  (1539, 148), (1784, 348), (1870, 183), (2777, 492), (3029, 1819),
  (3203, 999), (3281, 220), (3681, 793), (3726, 88), (3771, 791),
  (3975, 383), (4192, 892), (4237, 113), (4370, 717), (4486, 445),
  (4749, 154), (5843, 990), (6161, 217), (6447, 1492), (6450, 7),
  (6551, 224), (6587, 500), (7089, 158), (7111, 15), (7212, 261),
  (7231, 17), (7491, 795), (7826, 1358), (7903, 295), (7946, 1348),
  (8065, 1228), (8182, 891), (8626, 446), (9297, 1495), (9647, 498),
  (9751, 19), (10065, 381), (10083, 35), (10114, 54), (10218, 564),
  (10234, 56), (10876, 448), (10925, 75), (11029, 631), (11045, 67),
  (11188, 1655), (11276, 1359), (11393, 996), (11819, 1824), (12218, 135),
  (12275, 77), (12712, 885), (12760, 184), (12864, 1095), (12880, 186)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0X0Y0_check. -/
theorem X0Split72A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0X0Y0_pairs. -/
theorem X0Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split72A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0X0_pairs. -/
theorem X0Split72A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split72A0_pairs. -/
theorem X0Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split72_check. -/
theorem X0Split72_check : checkSplit m4TX0 (2, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0X0Y0_check. -/
theorem X0Split73A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0X0Y0_pairs. -/
theorem X0Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split73A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0X0_pairs. -/
theorem X0Split73A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split73A0_pairs. -/
theorem X0Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 6 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split73_check. -/
theorem X0Split73_check : checkSplit m4TX0 (2, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split74A0X0Y0Certs : List (Nat × Nat) := [
  (214, 1296), (694, 1809), (726, 1213), (809, 1750), (1390, 1435),
  (1825, 1959), (1895, 1487), (2017, 1131)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X0Y0_check. -/
theorem X0Split74A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X0Y0_pairs. -/
theorem X0Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split74A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X0_pairs. -/
theorem X0Split74A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split74A0X1Y0Certs : List (Nat × Nat) := [
  (632, 1972), (1036, 1074), (1141, 1716), (1247, 438), (1641, 881),
  (1882, 1600), (1970, 939)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X1Y0_check. -/
theorem X0Split74A0X1Y0_check : checkGrid m4TX0 censusX0 1 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split74A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X1Y0_pairs. -/
theorem X0Split74A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split74A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split74A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0X1_pairs. -/
theorem X0Split74A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split74A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74A0_pairs. -/
theorem X0Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 5 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split74A0X0_pairs x hx y hy hw
  · exact X0Split74A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split74_check. -/
theorem X0Split74_check : checkSplit m4TX0 (3, 0, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split74A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split75A0X0Y0Certs : List (Nat × Nat) := [
  (3603, 359), (4149, 1971), (4792, 1137), (5431, 1925), (5726, 1459),
  (5910, 756), (8915, 1616), (12329, 1864), (17047, 747), (19005, 1797),
  (20186, 583), (20781, 884), (20798, 322), (22504, 1413), (22996, 1612),
  (23015, 1543), (23402, 1307), (24267, 1725), (27257, 1209), (28599, 1910),
  (30550, 1945), (34403, 1434), (36011, 1405), (37931, 703), (40917, 1520),
  (42131, 698), (42214, 1806), (44664, 1124), (47473, 1291), (49462, 1958),
  (51201, 774), (52895, 288), (53325, 1293), (54661, 1337), (54704, 685),
  (57999, 963), (58702, 1895), (58720, 1903), (59286, 1782), (60509, 1146)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X0Y0_check. -/
theorem X0Split75A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X0Y0_pairs. -/
theorem X0Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split75A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X0_pairs. -/
theorem X0Split75A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split75A0X1Y0Certs : List (Nat × Nat) := [
  (364, 1810), (436, 871), (3886, 1589), (9447, 1199), (12677, 880),
  (15497, 1215), (18945, 441), (20809, 1729), (22411, 1334), (22450, 618),
  (23816, 1055), (25918, 1674), (28191, 1740), (30195, 1471), (30994, 1814),
  (31040, 1189), (34227, 1747), (35936, 245), (35956, 856), (36672, 1767),
  (37391, 701), (39430, 1076), (39533, 1484), (40919, 332), (45653, 1270),
  (47783, 1456), (49042, 955), (52231, 1331), (55281, 1559), (56379, 1851),
  (56425, 1344), (57995, 543), (58067, 1212), (59099, 918), (60288, 614)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X1Y0_check. -/
theorem X0Split75A0X1Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split75A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X1Y0_pairs. -/
theorem X0Split75A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split75A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S2048Chunk1 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split75A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0X1_pairs. -/
theorem X0Split75A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split75A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75A0_pairs. -/
theorem X0Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split75A0X0_pairs x hx y hy hw
  · exact X0Split75A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split75_check. -/
theorem X0Split75_check : checkSplit m4TX0 (3, 1, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split75A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X0Y0Certs : List (Nat × Nat) := [
  (513, 1899), (9837, 938), (18878, 476), (27497, 601), (28576, 1164),
  (30208, 1205), (32785, 1151), (50948, 171), (51452, 1117), (52513, 546),
  (53995, 906), (56562, 1170), (64451, 1697), (69306, 832), (74418, 436),
  (82759, 1645), (83989, 1791), (85872, 206)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X0Y0_check. -/
theorem X0Split76A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X0Y0_pairs. -/
theorem X0Split76A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk0 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X0_pairs. -/
theorem X0Split76A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X1Y0Certs : List (Nat × Nat) := [
  (5942, 1602), (8636, 1433), (34334, 769), (40058, 1595), (47262, 954),
  (48575, 1661), (69897, 1263), (80234, 573), (81727, 1036), (82891, 1872),
  (85567, 1006), (95343, 755)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X1Y0_check. -/
theorem X0Split76A0X1Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X1Y0_pairs. -/
theorem X0Split76A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk1 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X1_pairs. -/
theorem X0Split76A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X2Y0Certs : List (Nat × Nat) := [
  (21064, 1135), (26688, 1018), (44069, 419), (45042, 200), (49552, 1080),
  (56688, 1382), (66171, 1122), (69736, 477), (79865, 1688), (86293, 661),
  (94658, 580)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X2Y0_check. -/
theorem X0Split76A0X2Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X2Y0_pairs. -/
theorem X0Split76A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X2Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk2_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk2 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X2_pairs. -/
theorem X0Split76A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X3Y0Certs : List (Nat × Nat) := [
  (1487, 778), (5588, 987), (5857, 138), (14359, 1536), (16631, 878),
  (25292, 1775), (38064, 1850), (40558, 180), (43788, 482), (55739, 1432)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X3Y0_check. -/
theorem X0Split76A0X3Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X3Y0_pairs. -/
theorem X0Split76A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X3Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk3_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk3 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X3_pairs. -/
theorem X0Split76A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X4Y0Certs : List (Nat × Nat) := [
  (11489, 1287), (22759, 1974), (33056, 1181), (46064, 1258), (59810, 1599)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X4Y0_check. -/
theorem X0Split76A0X4Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X4Y0_pairs. -/
theorem X0Split76A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X4Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk4_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk4 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X4_pairs. -/
theorem X0Split76A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X5Y0Certs : List (Nat × Nat) := [
  (22218, 1326), (27784, 1269), (38391, 1966), (50689, 1271), (50964, 1458),
  (53263, 144)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X5Y0_check. -/
theorem X0Split76A0X5Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X5Y0_pairs. -/
theorem X0Split76A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X5Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk5_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk5 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X5_pairs. -/
theorem X0Split76A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X6Y0Certs : List (Nat × Nat) := [
  (27394, 1078), (30454, 1728), (44497, 406), (49899, 98), (51374, 1578),
  (54281, 855), (58246, 1518), (60845, 586), (73253, 1303)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X6Y0_check. -/
theorem X0Split76A0X6Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X6Y0_pairs. -/
theorem X0Split76A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X6Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk6_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk6 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X6_pairs. -/
theorem X0Split76A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X7Y0Certs : List (Nat × Nat) := [
  (579, 1715), (13236, 734), (14480, 1526), (33835, 1763), (55540, 575),
  (64381, 1548), (68927, 1134), (89861, 850), (90817, 467)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X7Y0_check. -/
theorem X0Split76A0X7Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X7Y0_pairs. -/
theorem X0Split76A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X7Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk7_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk7 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X7_pairs. -/
theorem X0Split76A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X8Y0Certs : List (Nat × Nat) := [
  (18554, 1638), (34644, 176), (38104, 481), (54942, 317), (60285, 957),
  (62960, 1723), (68066, 142), (75619, 527), (85380, 1158), (97372, 270)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X8Y0_check. -/
theorem X0Split76A0X8Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X8Y0_pairs. -/
theorem X0Split76A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X8Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk8_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk8 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X8_pairs. -/
theorem X0Split76A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X9Y0Certs : List (Nat × Nat) := [
  (1749, 1017), (2656, 1970), (10298, 1278), (22614, 1455), (22938, 364),
  (43960, 1890), (48491, 1254), (62354, 1703), (67007, 1909), (81016, 427),
  (84055, 588), (85468, 439), (89331, 970), (106720, 1142)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X9Y0_check. -/
theorem X0Split76A0X9Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X9Y0_pairs. -/
theorem X0Split76A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X9Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk9_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk9 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X9_pairs. -/
theorem X0Split76A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X10Y0Certs : List (Nat × Nat) := [
  (6426, 405), (17920, 870), (44670, 1138), (57521, 1789), (65282, 1745),
  (71759, 373), (81567, 1689), (93949, 1407), (99022, 1748), (99340, 1541),
  (101944, 541), (103402, 374)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X10Y0_check. -/
theorem X0Split76A0X10Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X10Y0_pairs. -/
theorem X0Split76A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X10Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk10_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk10 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X10_pairs. -/
theorem X0Split76A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X11Y0_check. -/
theorem X0Split76A0X11Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X11Y0_pairs. -/
theorem X0Split76A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X11Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk11_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk11 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X11_pairs. -/
theorem X0Split76A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X12Y0Certs : List (Nat × Nat) := [
  (158, 941), (64870, 1633), (70495, 1200), (90289, 833), (91632, 1777),
  (98268, 277), (99734, 1861), (101270, 929), (104636, 953), (108929, 1862)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X12Y0_check. -/
theorem X0Split76A0X12Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X12Y0_pairs. -/
theorem X0Split76A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X12Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk12_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk12 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X12_pairs. -/
theorem X0Split76A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X13Y0Certs : List (Nat × Nat) := [
  (3079, 316)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X13Y0_check. -/
theorem X0Split76A0X13Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X13Y0_pairs. -/
theorem X0Split76A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X13Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk13_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk13 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X13_pairs. -/
theorem X0Split76A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X14Y0Certs : List (Nat × Nat) := [
  (9457, 368), (10446, 1073), (24189, 491), (30406, 780), (50989, 1990),
  (69055, 1173), (75248, 590), (76149, 432), (81273, 968), (105954, 674)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X14Y0_check. -/
theorem X0Split76A0X14Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X14Y0_pairs. -/
theorem X0Split76A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X14Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk14_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk14 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X14_pairs. -/
theorem X0Split76A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X15Y0Certs : List (Nat × Nat) := [
  (2967, 1464), (6493, 1133), (13040, 1047), (14887, 1659), (25898, 877)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X15Y0_check. -/
theorem X0Split76A0X15Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X15Y0_pairs. -/
theorem X0Split76A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X15Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk15_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk15 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X15_pairs. -/
theorem X0Split76A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X16Y0Certs : List (Nat × Nat) := [
  (2682, 1290), (10918, 1547), (16654, 1737), (31303, 1585), (36796, 1756),
  (57782, 1514), (58233, 759), (85211, 486), (89697, 1079), (96892, 1709)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X16Y0_check. -/
theorem X0Split76A0X16Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X16Y0_pairs. -/
theorem X0Split76A0X16Y0_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X16Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk16_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk16_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk16 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk16_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk16_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X16_pairs. -/
theorem X0Split76A0X16_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X17Y0Certs : List (Nat × Nat) := [
  (5927, 757), (13744, 247), (19354, 864), (23695, 353), (25965, 882),
  (29601, 1474), (40288, 663)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X17Y0_check. -/
theorem X0Split76A0X17Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X17Y0_pairs. -/
theorem X0Split76A0X17Y0_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X17Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk17_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk17_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk17 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk17_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk17_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X17_pairs. -/
theorem X0Split76A0X17_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X18Y0Certs : List (Nat × Nat) := [
  (939, 1727), (3525, 1437), (28682, 937), (45762, 351), (57189, 1483),
  (69061, 1248), (92003, 603)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X18Y0_check. -/
theorem X0Split76A0X18Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X18Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X18Y0_pairs. -/
theorem X0Split76A0X18Y0_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X18Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk18_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk18_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk18 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk18_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk18_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X18Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X18_pairs. -/
theorem X0Split76A0X18_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X18Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X19Y0Certs : List (Nat × Nat) := [
  (8403, 1896), (10670, 667), (30794, 607), (33443, 1423), (36402, 1938),
  (38180, 1457), (42050, 694), (46391, 649), (48388, 672)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X19Y0_check. -/
theorem X0Split76A0X19Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X19Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X19Y0_pairs. -/
theorem X0Split76A0X19Y0_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X19Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk19_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk19_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk19 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk19_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk19_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X19Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X19_pairs. -/
theorem X0Split76A0X19_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X19Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X20Y0Certs : List (Nat × Nat) := [
  (1777, 1089), (16695, 1720), (37963, 1908), (41253, 545), (43113, 1129),
  (48525, 1284), (67394, 824), (71069, 1954), (78073, 1171), (79963, 1377),
  (108738, 1853), (108780, 1313)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X20Y0_check. -/
theorem X0Split76A0X20Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X20Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X20Y0_pairs. -/
theorem X0Split76A0X20Y0_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X20Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk20_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk20_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk20 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk20_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk20_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X20Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X20_pairs. -/
theorem X0Split76A0X20_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X20Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split76A0X21Y0Certs : List (Nat × Nat) := [
  (15199, 1783), (22992, 1160), (24894, 978), (30201, 1636), (51270, 1308),
  (54890, 576), (60351, 738), (62585, 1320)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X21Y0_check. -/
theorem X0Split76A0X21Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X21Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X21Y0_pairs. -/
theorem X0Split76A0X21Y0_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split76A0X21Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk21_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M1Left_bound x (outerMasks3S256Chunk21_bound x hx)
  · intro y hy
    exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 1 outerMasks3S256Chunk21 masks2S512Chunk0
      X0M1LeftColumns X0M1RightColumns
    · decide
    · exact outerMasks3S256Chunk21_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M1Left_eq
    · exact X0M1Right_eq
    · intro x hx
      exact X0M1Left_bound x (outerMasks3S256Chunk21_bound x hx)
    · intro y hy
      exact X0M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split76A0X21Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0X21_pairs. -/
theorem X0Split76A0X21_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split76A0X21Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76A0_pairs. -/
theorem X0Split76A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact X0Split76A0X0_pairs x hx y hy hw
  · exact X0Split76A0X1_pairs x hx y hy hw
  · exact X0Split76A0X2_pairs x hx y hy hw
  · exact X0Split76A0X3_pairs x hx y hy hw
  · exact X0Split76A0X4_pairs x hx y hy hw
  · exact X0Split76A0X5_pairs x hx y hy hw
  · exact X0Split76A0X6_pairs x hx y hy hw
  · exact X0Split76A0X7_pairs x hx y hy hw
  · exact X0Split76A0X8_pairs x hx y hy hw
  · exact X0Split76A0X9_pairs x hx y hy hw
  · exact X0Split76A0X10_pairs x hx y hy hw
  · exact X0Split76A0X11_pairs x hx y hy hw
  · exact X0Split76A0X12_pairs x hx y hy hw
  · exact X0Split76A0X13_pairs x hx y hy hw
  · exact X0Split76A0X14_pairs x hx y hy hw
  · exact X0Split76A0X15_pairs x hx y hy hw
  · exact X0Split76A0X16_pairs x hx y hy hw
  · exact X0Split76A0X17_pairs x hx y hy hw
  · exact X0Split76A0X18_pairs x hx y hy hw
  · exact X0Split76A0X19_pairs x hx y hy hw
  · exact X0Split76A0X20_pairs x hx y hy hw
  · exact X0Split76A0X21_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split76_check. -/
theorem X0Split76_check : checkSplit m4TX0 (3, 2, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X0Y0Certs : List (Nat × Nat) := [
  (6892, 1554), (27823, 1857), (27875, 145), (28553, 1104), (32906, 1115),
  (56779, 866), (61426, 349), (64373, 1918), (64765, 1671), (68702, 1832),
  (78089, 843), (83822, 1236), (87268, 1049), (92112, 1364)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X0Y0_check. -/
theorem X0Split77A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X0Y0_pairs. -/
theorem X0Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X0_pairs. -/
theorem X0Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X1Y0Certs : List (Nat × Nat) := [
  (25139, 1430), (32826, 743), (48674, 1687), (59965, 1584), (62880, 915),
  (80204, 594), (81014, 375), (81363, 100), (95313, 198), (97078, 279)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X1Y0_check. -/
theorem X0Split77A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X1Y0_pairs. -/
theorem X0Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X1_pairs. -/
theorem X0Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X2Y0Certs : List (Nat × Nat) := [
  (14332, 1844), (39632, 196), (41103, 803), (66397, 1103), (80667, 728),
  (85161, 1383), (86216, 320), (93149, 238)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X2Y0_check. -/
theorem X0Split77A0X2Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X2Y0_pairs. -/
theorem X0Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X2Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk2_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk2 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X2_pairs. -/
theorem X0Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X3Y0Certs : List (Nat × Nat) := [
  (1472, 611), (5198, 1845), (6608, 311), (23681, 727), (25580, 1478),
  (39534, 1667), (40895, 43), (45612, 1604), (53960, 105), (54590, 807)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X3Y0_check. -/
theorem X0Split77A0X3Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X3Y0_pairs. -/
theorem X0Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X3Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk3_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk3 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X3_pairs. -/
theorem X0Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X4Y0Certs : List (Nat × Nat) := [
  (5816, 587), (11741, 1965), (19150, 78), (25127, 1371), (54487, 409),
  (62051, 1116)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X4Y0_check. -/
theorem X0Split77A0X4Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X4Y0_pairs. -/
theorem X0Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X4Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk4_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk4 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X4_pairs. -/
theorem X0Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X5Y0Certs : List (Nat × Nat) := [
  (10001, 1964), (17109, 525), (19022, 1281), (26677, 520), (53214, 526),
  (71335, 1952)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X5Y0_check. -/
theorem X0Split77A0X5Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X5Y0_pairs. -/
theorem X0Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X5Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk5_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk5 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X5_pairs. -/
theorem X0Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X6Y0Certs : List (Nat × Nat) := [
  (3820, 1399), (5405, 677), (23071, 94), (31085, 742), (46280, 627),
  (49726, 504), (51104, 781), (51403, 280), (60619, 568), (73207, 465),
  (76291, 605), (79485, 1267)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X6Y0_check. -/
theorem X0Split77A0X6Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X6Y0_pairs. -/
theorem X0Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X6Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk6_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk6 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X6_pairs. -/
theorem X0Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X7Y0Certs : List (Nat × Nat) := [
  (6462, 1603), (15243, 99), (35606, 1593), (43577, 292), (70159, 459),
  (76049, 1521), (83646, 463), (85717, 114)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X7Y0_check. -/
theorem X0Split77A0X7Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X7Y0_pairs. -/
theorem X0Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X7Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk7_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk7 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X7_pairs. -/
theorem X0Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X8Y0Certs : List (Nat × Nat) := [
  (2318, 522), (8980, 1111), (13383, 1376), (19798, 836), (54819, 63),
  (70420, 1673), (77301, 1245), (82356, 514), (85445, 678), (95410, 528)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X8Y0_check. -/
theorem X0Split77A0X8Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X8Y0_pairs. -/
theorem X0Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X8Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk8_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk8 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X8_pairs. -/
theorem X0Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X9Y0Certs : List (Nat × Nat) := [
  (10195, 723), (21404, 335), (26001, 1384), (28758, 199), (29761, 662),
  (59029, 1242), (62588, 1664), (68229, 1576), (82289, 283), (85722, 126),
  (91322, 1831), (104476, 290), (104881, 195)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X9Y0_check. -/
theorem X0Split77A0X9Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X9Y0_pairs. -/
theorem X0Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X9Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk9_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk9 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X9_pairs. -/
theorem X0Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X10Y0Certs : List (Nat × Nat) := [
  (9990, 1865), (19431, 1153), (27681, 1101), (36059, 1686), (44592, 829),
  (48987, 1042), (51731, 1760), (52258, 235), (64645, 1034), (71414, 284),
  (103362, 1044)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X10Y0_check. -/
theorem X0Split77A0X10Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X10Y0_pairs. -/
theorem X0Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X10Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk10_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk10 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X10_pairs. -/
theorem X0Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X11Y0Certs : List (Nat × Nat) := [
  (5030, 943)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X11Y0_check. -/
theorem X0Split77A0X11Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X11Y0_pairs. -/
theorem X0Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X11Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk11_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk11 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X11_pairs. -/
theorem X0Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X12Y0Certs : List (Nat × Nat) := [
  (7203, 928), (18485, 806), (22481, 1177), (34447, 309), (41982, 831),
  (55686, 59), (58360, 269), (71221, 1277), (91594, 934), (93343, 1002),
  (98130, 1003), (99504, 1339), (99781, 604)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X12Y0_check. -/
theorem X0Split77A0X12Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X12Y0_pairs. -/
theorem X0Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X12Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk12_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk12 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X12_pairs. -/
theorem X0Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X13Y0Certs : List (Nat × Nat) := [
  (3051, 57), (14091, 640), (17799, 1743)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X13Y0_check. -/
theorem X0Split77A0X13Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X13Y0_pairs. -/
theorem X0Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X13Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk13_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk13 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X13_pairs. -/
theorem X0Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X14Y0Certs : List (Nat × Nat) := [
  (12011, 1040), (28615, 1397), (30386, 1594), (33099, 165), (39671, 319),
  (42291, 356), (46378, 1048), (53242, 641), (68848, 428), (86241, 403),
  (96489, 1511), (105748, 174)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X14Y0_check. -/
theorem X0Split77A0X14Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X14Y0_pairs. -/
theorem X0Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X14Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk14_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk14 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X14_pairs. -/
theorem X0Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X15Y0Certs : List (Nat × Nat) := [
  (10268, 1022), (15615, 1691), (24030, 390), (25961, 1176)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X15Y0_check. -/
theorem X0Split77A0X15Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X15Y0_pairs. -/
theorem X0Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X15Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk15_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk15 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X15_pairs. -/
theorem X0Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X16Y0Certs : List (Nat × Nat) := [
  (9541, 1829), (15320, 352), (36842, 1234), (39103, 1682), (56303, 705),
  (60810, 1438), (63216, 516), (67552, 466), (69457, 1159), (96502, 1553),
  (110007, 1681)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X16Y0_check. -/
theorem X0Split77A0X16Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X16Y0_pairs. -/
theorem X0Split77A0X16Y0_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X16Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk16_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk16 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk16_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X16_pairs. -/
theorem X0Split77A0X16_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X17Y0Certs : List (Nat × Nat) := [
  (5708, 208), (10172, 612), (26190, 337), (30944, 236), (38014, 620),
  (38404, 460)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X17Y0_check. -/
theorem X0Split77A0X17Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X17Y0_pairs. -/
theorem X0Split77A0X17Y0_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X17Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk17_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk17 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk17_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X17_pairs. -/
theorem X0Split77A0X17_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X18Y0Certs : List (Nat × Nat) := [
  (381, 1662), (1214, 1429), (16448, 1510), (30793, 1422), (41972, 801),
  (47258, 1105), (50941, 194), (52600, 1755), (57723, 1239), (69033, 1238),
  (76305, 656), (87154, 570), (92142, 1515), (106613, 162), (109347, 589)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X18Y0_check. -/
theorem X0Split77A0X18Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X18Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X18Y0_pairs. -/
theorem X0Split77A0X18Y0_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X18Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk18_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk18 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk18_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X18Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X18_pairs. -/
theorem X0Split77A0X18_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X18Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X19Y0Certs : List (Nat × Nat) := [
  (1334, 137), (10611, 638), (48323, 161)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X19Y0_check. -/
theorem X0Split77A0X19Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X19Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X19Y0_pairs. -/
theorem X0Split77A0X19Y0_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X19Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk19_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk19 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk19_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X19Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X19_pairs. -/
theorem X0Split77A0X19_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X19Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X20Y0Certs : List (Nat × Nat) := [
  (2365, 725), (6769, 935), (28944, 900), (34857, 232), (45439, 737),
  (60023, 1917), (77976, 404), (79989, 1668), (81908, 469), (93756, 898),
  (102900, 913), (107309, 1216)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X20Y0_check. -/
theorem X0Split77A0X20Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X20Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X20Y0_pairs. -/
theorem X0Split77A0X20Y0_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X20Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk20_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk20 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk20_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X20Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X20_pairs. -/
theorem X0Split77A0X20_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X20Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split77A0X21Y0Certs : List (Nat × Nat) := [
  (3350, 1243), (6788, 1021), (15041, 974), (31868, 414), (51029, 484),
  (55825, 529), (62829, 707)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X21Y0_check. -/
theorem X0Split77A0X21Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X21Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X21Y0_pairs. -/
theorem X0Split77A0X21Y0_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split77A0X21Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk21_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S256Chunk21 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S256Chunk21_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X0Split77A0X21Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0X21_pairs. -/
theorem X0Split77A0X21_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split77A0X21Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77A0_pairs. -/
theorem X0Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact X0Split77A0X0_pairs x hx y hy hw
  · exact X0Split77A0X1_pairs x hx y hy hw
  · exact X0Split77A0X2_pairs x hx y hy hw
  · exact X0Split77A0X3_pairs x hx y hy hw
  · exact X0Split77A0X4_pairs x hx y hy hw
  · exact X0Split77A0X5_pairs x hx y hy hw
  · exact X0Split77A0X6_pairs x hx y hy hw
  · exact X0Split77A0X7_pairs x hx y hy hw
  · exact X0Split77A0X8_pairs x hx y hy hw
  · exact X0Split77A0X9_pairs x hx y hy hw
  · exact X0Split77A0X10_pairs x hx y hy hw
  · exact X0Split77A0X11_pairs x hx y hy hw
  · exact X0Split77A0X12_pairs x hx y hy hw
  · exact X0Split77A0X13_pairs x hx y hy hw
  · exact X0Split77A0X14_pairs x hx y hy hw
  · exact X0Split77A0X15_pairs x hx y hy hw
  · exact X0Split77A0X16_pairs x hx y hy hw
  · exact X0Split77A0X17_pairs x hx y hy hw
  · exact X0Split77A0X18_pairs x hx y hy hw
  · exact X0Split77A0X19_pairs x hx y hy hw
  · exact X0Split77A0X20_pairs x hx y hy hw
  · exact X0Split77A0X21_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split77_check. -/
theorem X0Split77_check : checkSplit m4TX0 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split78A0X0Y0Certs : List (Nat × Nat) := [
  (5336, 1355), (5639, 1827), (11271, 789), (12010, 191), (12014, 344),
  (12041, 219), (14311, 9), (16494, 1096), (16952, 25), (16967, 499),
  (17161, 16), (21935, 74), (22871, 225), (25445, 71), (25448, 130),
  (30189, 155), (30902, 27), (33828, 561), (33839, 1817), (35671, 12),
  (36344, 346), (37426, 447), (37430, 722), (37487, 494), (40889, 1823),
  (41091, 788), (42364, 50), (45813, 37), (47016, 91), (47033, 998),
  (47128, 1657), (47734, 51), (49085, 66), (50955, 389), (54184, 55),
  (54187, 109), (54995, 68), (55463, 997), (57100, 182), (57822, 259),
  (58547, 495)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X0Y0_check. -/
theorem X0Split78A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X0Y0_pairs. -/
theorem X0Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split78A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X0_pairs. -/
theorem X0Split78A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split78A0X1Y0Certs : List (Nat × Nat) := [
  (1339, 636), (1350, 1), (1361, 216), (3285, 388), (4446, 87),
  (10657, 108), (12046, 449), (12154, 52), (13190, 720), (14782, 888),
  (14785, 1231), (14873, 994), (16911, 787), (16914, 1100), (18651, 796),
  (19992, 260), (20007, 1501), (20198, 132), (21146, 1354), (21249, 156),
  (23290, 185), (23835, 378), (27678, 559), (28751, 214), (30159, 149),
  (30163, 300), (31510, 187), (32157, 1503), (34516, 443), (35662, 896),
  (35783, 995), (39596, 1350), (39598, 1658), (40767, 1499), (41185, 1230),
  (41731, 13), (41733, 32), (42823, 299), (44812, 893), (44949, 157),
  (51300, 4), (53096, 1349), (53177, 496), (55185, 379), (55189, 637),
  (55317, 1500), (56519, 1826), (57076, 451), (58672, 887)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X1Y0_check. -/
theorem X0Split78A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split78A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X1Y0_pairs. -/
theorem X0Split78A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split78A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S2048Chunk1 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split78A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0X1_pairs. -/
theorem X0Split78A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split78A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78A0_pairs. -/
theorem X0Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split78A0X0_pairs x hx y hy hw
  · exact X0Split78A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split78_check. -/
theorem X0Split78_check : checkSplit m4TX0 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X0Y0_check. -/
theorem X0Split79A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X0Y0_pairs. -/
theorem X0Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split79A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X0_pairs. -/
theorem X0Split79A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split79A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X1Y0_check. -/
theorem X0Split79A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split79A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X1Y0_pairs. -/
theorem X0Split79A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split79A0X1Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 0 outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M0Left_eq
    · exact X0M0Right_eq
    · intro x hx
      exact X0M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X0M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split79A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0X1_pairs. -/
theorem X0Split79A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split79A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79A0_pairs. -/
theorem X0Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split79A0X0_pairs x hx y hy hw
  · exact X0Split79A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split79_check. -/
theorem X0Split79_check : checkSplit m4TX0 (3, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X0M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X0Split79A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150
